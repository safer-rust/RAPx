#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_assignments)]
#![allow(irrefutable_let_patterns)]
use std::{default, fmt};

use num_traits::{Bounded, Num, Zero};
use rust_intervals::Interval;
use rustc_middle::mir::{BinOp, UnOp};
use std::ops::{Add, Mul, Sub};

use crate::{
    analysis::range_analysis::{Range, RangeType, domain::symbolic_expr::IntervalTypeTrait},
    rap_trace,
};

use super::domain::*;

impl<T> Range<T>
where
    T: IntervalArithmetic,
{
    // Parameterized constructor
    pub fn new(lb: T, ub: T, rtype: RangeType) -> Self {
        Self {
            rtype,
            range: Interval::new_closed_closed(lb, ub),
        }
    }
    pub fn default(default: T) -> Self {
        Self {
            rtype: RangeType::Unknown,

            range: Interval::new_closed_closed(default, default),
        }
    }
    // Getter for lower bound
    pub fn init(r: Interval<T>) -> Self {
        Self {
            rtype: RangeType::Regular,
            range: r,
        }
    }

    pub fn top() -> Self {
        Self::new(T::min_value(), T::max_value(), RangeType::Regular)
    }

    pub fn bottom() -> Self {
        Self::default(T::min_value())
    }

    pub fn exact(value: T) -> Self {
        Self::new(value.clone(), value, RangeType::Regular)
    }

    pub fn get_lower(&self) -> T {
        self.range.lower().unwrap().clone()
    }

    // Getter for upper bound
    pub fn get_upper(&self) -> T {
        self.range.upper().unwrap().clone()
    }

    // Check if the range type is unknown
    pub fn is_unknown(&self) -> bool {
        self.rtype == RangeType::Unknown
    }

    // Set the range type to unknown
    pub fn set_unknown(&mut self) {
        self.rtype = RangeType::Unknown;
    }

    // Check if the range type is regular
    pub fn is_regular(&self) -> bool {
        self.rtype == RangeType::Regular
    }

    // Set the range type to regular
    pub fn set_regular(&mut self) {
        self.rtype = RangeType::Regular;
    }

    // Check if the range type is empty
    pub fn is_empty(&self) -> bool {
        self.rtype == RangeType::Empty
    }

    // Set the range type to empty
    pub fn set_empty(&mut self) {
        self.rtype = RangeType::Empty;
    }
    pub fn set_default(&mut self) {
        self.rtype = RangeType::Regular;
        self.range = Interval::new_closed_closed(T::min_value(), T::max_value());
    }
    pub fn add(&self, other: &Range<T>) -> Range<T> {
        let a = self
            .get_lower()
            .clone()
            .checked_add(&other.get_lower().clone())
            .unwrap_or(T::max_value());

        let b = self
            .get_upper()
            .clone()
            .checked_add(&other.get_upper().clone())
            .unwrap_or(T::max_value());

        Range::new(a, b, RangeType::Regular)
    }

    pub fn sub(&self, other: &Range<T>) -> Range<T> {
        let a = self
            .get_lower()
            .clone()
            .checked_sub(&other.get_upper().clone())
            .unwrap_or(T::min_value());

        let b = self
            .get_upper()
            .clone()
            .checked_sub(&other.get_lower().clone())
            .unwrap_or(T::max_value());

        Range::new(a, b, RangeType::Regular)
    }

    pub fn mul(&self, other: &Range<T>) -> Range<T> {
        let candidates = vec![
            self.get_lower().clone() * other.get_lower().clone(),
            self.get_lower().clone() * other.get_upper().clone(),
            self.get_upper().clone() * other.get_lower().clone(),
            self.get_upper().clone() * other.get_upper().clone(),
        ];
        let min = candidates
            .iter()
            .cloned()
            .min_by(|a, b| a.partial_cmp(b).unwrap())
            .unwrap();
        let max = candidates
            .iter()
            .cloned()
            .max_by(|a, b| a.partial_cmp(b).unwrap())
            .unwrap();
        Range::new(min, max, RangeType::Regular)
    }

    pub fn intersectwith(&self, other: &Range<T>) -> Range<T> {
        if self.is_unknown() {
            return Range::new(
                other.get_lower().clone(),
                other.get_upper().clone(),
                RangeType::Regular,
            );
        } else if other.is_unknown() {
            return Range::new(
                self.get_lower().clone(),
                self.get_upper().clone(),
                RangeType::Regular,
            );
        } else {
            let result = self.range.clone().intersection(&other.range.clone());
            let mut range = Range::bottom();

            if let r = result {
                range = Range::init(r);
                range
            } else {
                range
            }
        }
    }

    pub fn unionwith(&self, other: &Range<T>) -> Range<T> {
        if self.is_unknown() {
            return Range::new(
                other.get_lower().clone(),
                other.get_upper().clone(),
                RangeType::Regular,
            );
        } else if other.is_unknown() {
            return Range::new(
                self.get_lower().clone(),
                self.get_upper().clone(),
                RangeType::Regular,
            );
        } else {
            let left = std::cmp::min_by(self.get_lower(), other.get_lower(), |a, b| {
                a.partial_cmp(b).unwrap()
            });
            let right = std::cmp::max_by(self.get_upper(), other.get_upper(), |a, b| {
                a.partial_cmp(b).unwrap()
            });
            Range::new(left.clone(), right.clone(), RangeType::Regular)
        }
    }
}

pub trait Lattice {
    fn widen(&self, other: &Self) -> Self;
    fn narrow(&self, other: &Self) -> Self;
}

impl<T> Range<T>
where
    T: IntervalArithmetic,
{
    pub fn widen(&self, other: &Range<T>) -> Range<T> {
        if self.is_unknown() {
            return other.clone();
        }
        let a_lower = self.get_lower();
        let a_upper = self.get_upper();
        let b_lower = other.get_lower();
        let b_upper = other.get_upper();

        if b_lower < a_lower && b_upper > a_upper {
            Range::top()
        } else if b_lower < a_lower {
            Range::new(T::min_value(), a_upper.clone(), RangeType::Regular)
        } else if b_upper > a_upper {
            Range::new(a_lower.clone(), T::max_value(), RangeType::Regular)
        } else {
            self.clone()
        }
    }

    pub fn narrow(&self, other: &Range<T>) -> Range<T> {
        let a_lower = self.get_lower();
        let a_upper = self.get_upper();
        let b_lower = other.get_lower();
        let b_upper = other.get_upper();

        let final_lower = if a_lower == T::min_value() && b_lower > T::min_value() {
            b_lower.clone()
        } else if a_lower <= b_lower {
            b_lower.clone()
        } else {
            a_lower.clone()
        };

        let final_upper = if a_upper == T::max_value() && b_upper < T::max_value() {
            b_upper.clone()
        } else if a_upper >= b_upper {
            b_upper.clone()
        } else {
            a_upper.clone()
        };

        Range::new(final_lower, final_upper, RangeType::Regular)
    }
}

impl<T: IntervalArithmetic> Lattice for Range<T> {
    fn widen(&self, other: &Range<T>) -> Range<T> {
        Range::widen(self, other)
    }

    fn narrow(&self, other: &Range<T>) -> Range<T> {
        Range::narrow(self, other)
    }
}
