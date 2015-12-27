#![feature(zero_one,box_syntax)]

extern crate asexp;
extern crate expression;

use expression::{ExpressionError, Expression};
use std::ops::{Add, Sub, Mul, Div};
use std::num::{Zero, One};
use std::fmt::Debug;
use asexp::Sexp;

pub trait NumType: Debug + Copy + Clone + PartialEq + PartialOrd + Default + Zero + One +
Add<Output=Self> + Sub<Output=Self> + Mul<Output=Self> + Div<Output=Self> {}

impl NumType for f32 {}
impl NumType for f64 {}
impl NumType for u32 {}
impl NumType for u64 {}

/// An expression evaluates to a numeric value of type `NumType`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum NumExpr<T: NumType> {
    /// A constant value.
    Const(T),

    /// References a variable by position
    Var(usize),

    Add(Box<NumExpr<T>>, Box<NumExpr<T>>),
    Sub(Box<NumExpr<T>>, Box<NumExpr<T>>),
    Mul(Box<NumExpr<T>>, Box<NumExpr<T>>),
    Div(Box<NumExpr<T>>, Box<NumExpr<T>>),

    /// Safe division with x/0 = 0.0
    Divz(Box<NumExpr<T>>, Box<NumExpr<T>>),

    /// Reciprocal (1 / x).
    Recip(Box<NumExpr<T>>),

    /// Reciprocal using safe division
    Recipz(Box<NumExpr<T>>),
}

impl<T: NumType> Expression for NumExpr<T> {
    type Element = T;

    fn evaluate(&self, variables: &[Self::Element]) -> Result<Self::Element, ExpressionError> {
        Ok(match self {
            &NumExpr::Var(n) => {
                try!(variables.get(n).ok_or(ExpressionError::InvalidVariable)).clone()
            }
            &NumExpr::Const(val) => val,
            &NumExpr::Add(ref e1, ref e2) => {
                try!(e1.evaluate(variables)) + try!(e2.evaluate(variables))
            }
            &NumExpr::Sub(ref e1, ref e2) => {
                try!(e1.evaluate(variables)) - try!(e2.evaluate(variables))
            }
            &NumExpr::Mul(ref e1, ref e2) => {
                try!(e1.evaluate(variables)) * try!(e2.evaluate(variables))
            }
            &NumExpr::Div(ref e1, ref e2) => {
                let a = try!(e1.evaluate(variables));
                let div = try!(e2.evaluate(variables));
                if div == T::zero() {
                    return Err(ExpressionError::DivByZero);
                }
                a / div
            }
            &NumExpr::Divz(ref e1, ref e2) => {
                let a = try!(e1.evaluate(variables));
                let div = try!(e2.evaluate(variables));
                if div == T::zero() {
                    div
                } else {
                    a / div
                }
            }
            &NumExpr::Recip(ref e1) => {
                let div = try!(e1.evaluate(variables));
                if div == T::zero() {
                    return Err(ExpressionError::DivByZero);
                } else {
                    T::one() / div
                }
            }
            &NumExpr::Recipz(ref e1) => {
                let div = try!(e1.evaluate(variables));
                if div == T::zero() {
                    div
                } else {
                    T::one() / div
                }
            }
        })
    }
}

impl<'a, T: NumType + Into<Sexp>> Into<Sexp> for &'a NumExpr<T> {
    fn into(self) -> Sexp {
        match self {
            &NumExpr::Const(n) => n.into(),
            &NumExpr::Var(n) => Sexp::from(format!("${}", n)),
            &NumExpr::Add(ref a, ref b) => {
                Sexp::from(("+",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &NumExpr::Sub(ref a, ref b) => {
                Sexp::from(("-",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &NumExpr::Mul(ref a, ref b) => {
                Sexp::from(("*",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &NumExpr::Div(ref a, ref b) => {
                Sexp::from(("/",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &NumExpr::Divz(ref a, ref b) => {
                Sexp::from(("divz",
                            Into::<Sexp>::into(a.as_ref()),
                            Into::<Sexp>::into(b.as_ref())))
            }
            &NumExpr::Recip(ref a) => Sexp::from(("recip", Into::<Sexp>::into(a.as_ref()))),
            &NumExpr::Recipz(ref a) => Sexp::from(("recipz", Into::<Sexp>::into(a.as_ref()))),
        }
    }
}

#[cfg(test)]
const NO_VARS: [f32; 0] = [];

#[test]
fn test_expr_divz() {
    let expr = NumExpr::Divz(box NumExpr::Const(1.0), box NumExpr::Const(0.0));
    assert_eq!(Ok(0.0), expr.evaluate(&NO_VARS));
}

#[test]
fn test_expr_recipz() {
    let expr = NumExpr::Recipz(box NumExpr::Const(0.0));
    assert_eq!(Ok(0.0), expr.evaluate(&NO_VARS));

    let expr = NumExpr::Recipz(box NumExpr::Const(1.0));
    assert_eq!(Ok(1.0), expr.evaluate(&NO_VARS));

    let expr = NumExpr::Recipz(box NumExpr::Const(0.5));
    assert_eq!(Ok(2.0), expr.evaluate(&NO_VARS));
}

#[test]
fn test_expr() {
    let expr =
        NumExpr::Sub(box NumExpr::Const(0.0),
                     box NumExpr::Div(box NumExpr::Mul(box NumExpr::Add(box NumExpr::Const(1.0),
                                                                        box NumExpr::Var(0)),
                                                       box NumExpr::Var(1)),
                                      box NumExpr::Const(2.0)));

    fn fun(a: f32, b: f32) -> f32 {
        0.0 - ((1.0 + a) * b) / 2.0
    }

    fn check(expr: &NumExpr<f32>, a: f32, b: f32) {
        assert_eq!(Ok(fun(a, b)), expr.evaluate(&[a, b]))
    }

    check(&expr, 123.0, 4444.0);
    check(&expr, 0.0, -12.0);
}
