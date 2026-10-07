//! Executable feasibility fixtures for a future Rust axiom worker.
//!
//! Ownership-invalid term shapes are compiler errors, as required:
//!
//! ```compile_fail
//! use dig_axiom_spike::Stack;
//! let stack = Stack::from_recipe(&[1]);
//! let consumed = stack.into_pushed(2);
//! let _illegal_reuse = stack.len();
//! # drop(consumed);
//! ```

use std::cell::RefCell;

#[derive(Debug, Eq, PartialEq)]
pub struct Stack<T> {
    values: Vec<T>,
}

impl<T: Copy> Stack<T> {
    pub fn from_recipe(values: &[T]) -> Self {
        Self {
            values: values.to_vec(),
        }
    }

    pub fn push(&mut self, value: T) {
        self.values.push(value);
    }

    pub fn pop(&mut self) -> Option<T> {
        self.values.pop()
    }

    pub fn last(&self) -> Option<&T> {
        self.values.last()
    }

    pub fn into_pushed(mut self, value: T) -> Self {
        self.push(value);
        self
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    pub fn snapshot(&self) -> &[T] {
        &self.values
    }
}

pub trait Observer {
    fn observed_len(&self) -> usize;
}

impl<T> Observer for Vec<T> {
    fn observed_len(&self) -> usize {
        self.len()
    }
}

pub struct InteriorCounter {
    value: RefCell<i32>,
}

impl InteriorCounter {
    pub fn new(value: i32) -> Self {
        Self {
            value: RefCell::new(value),
        }
    }

    pub fn increment_through_shared_borrow(&self) {
        *self.value.borrow_mut() += 1;
    }

    pub fn snapshot(&self) -> i32 {
        *self.value.borrow()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic::{AssertUnwindSafe, catch_unwind};

    #[test]
    fn mutable_stack_law_reconstructs_two_worlds_without_clone() {
        let recipe = [1, 2];
        let mut lhs = Stack::from_recipe(&recipe);
        lhs.push(3);
        let result = lhs.pop();

        let rhs = Stack::from_recipe(&recipe);
        assert_eq!(result, Some(3));
        assert_eq!(lhs.snapshot(), rhs.snapshot());
    }

    #[test]
    fn owned_builder_consumes_and_returns_state() {
        let stack = Stack::from_recipe(&[1]);
        let stack = stack.into_pushed(2);
        assert_eq!(stack.snapshot(), &[1, 2]);
    }

    #[test]
    fn ordinary_panic_is_caught_at_case_boundary() {
        let result = catch_unwind(AssertUnwindSafe(|| {
            let mut stack = Stack::<i32>::from_recipe(&[]);
            stack.pop().unwrap()
        }));
        assert!(result.is_err());
    }

    #[test]
    fn concrete_trait_binding_is_statically_dispatched() {
        let values = vec![1, 2, 3];
        assert_eq!(Observer::observed_len(&values), 3);
    }

    #[test]
    fn option_and_result_are_ordinary_return_values() {
        let mut stack = Stack::from_recipe(&[1]);
        let option = stack.pop();
        let result: Result<i32, &str> = option.ok_or("empty");
        assert_eq!(result, Ok(1));
    }

    #[test]
    fn interior_mutability_is_visible_only_through_custom_snapshot() {
        let counter = InteriorCounter::new(1);
        counter.increment_through_shared_borrow();
        assert_eq!(counter.snapshot(), 2);
    }
}

