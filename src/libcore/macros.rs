// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![macro_escape]

/// Entry point of failure, for details, see std::macros
#[macro_export]
macro_rules! fail(
    () => (
        fail!("explicit failure")
    );
    ($msg:expr) => ({
        static _FILE_LINE: (&'static str, uint) = (file!(), line!());
        ::core::failure::begin_unwind_string($msg, &_FILE_LINE)
    });
    ($fmt:expr, $($arg:tt)*) => ({
        // a closure can't have return type !, so we need a full
        // function to pass to format_args!, *and* we need the
        // file and line numbers right here; so an inner bare fn
        // is our only choice.
        //
        // LLVM doesn't tend to inline this, presumably because begin_unwind_fmt
        // is #[cold] and #[inline(never)] and because this is flagged as cold
        // as returning !. We really do want this to be inlined, however,
        // because it's just a tiny wrapper. Small wins (156K to 149K in size)
        // were seen when forcing this to be inlined, and that number just goes
        // up with the number of calls to fail!()
        //
        // The leading _'s are to avoid dead code warnings if this is
        // used inside a dead function. Just `#[allow(dead_code)]` is
        // insufficient, since the user may have
        // `#[forbid(dead_code)]` and which cannot be overridden.
        #[inline(always)]
        fn _run_fmt(fmt: &::core::fmt::Arguments) -> ! {
            static _FILE_LINE: (&'static str, uint) = (file!(), line!());
            ::core::failure::begin_unwind(fmt, &_FILE_LINE)
        }
        format_args!(_run_fmt, $fmt, $($arg)*)
    });
)

/// A utility macro for indicating unreachable code. It will fail if
/// executed. This is occasionally useful to put after loops that never
/// terminate normally, but instead directly return from a function.
///
/// # Example
///
/// ~~~rust
/// struct Item { weight: uint }
///
/// fn choose_weighted_item(v: &[Item]) -> Item {
///     assert!(!v.is_empty());
///     let mut so_far = 0u;
///     for item in v.iter() {
///         so_far += item.weight;
///         if so_far > 100 {
///             return *item;
///         }
///     }
///     // The above loop always returns, so we must hint to the
///     // type checker that it isn't possible to get down here
///     unreachable!();
/// }
/// ~~~
#[macro_export]
macro_rules! unreachable(
    () => (fail!("internal error: entered unreachable code"))
)

/// Ensure that a boolean expression is `true` at runtime.
///
/// This will invoke the `fail!` macro if the provided expression cannot be
/// evaluated to `true` at runtime.
///
/// # Example
///
/// ```
/// // the failure message for these assertions is the stringified value of the
/// // expression given.
/// assert!(true);
/// # fn some_computation() -> bool { true }
/// assert!(some_computation());
///
/// // assert with a custom message
/// # let x = true;
/// assert!(x, "x wasn't true!");
/// # let a = 3i; let b = 27i;
/// assert!(a + b == 30, "a = {}, b = {}", a, b);
/// ```
#[macro_export]
macro_rules! assert(
    ($cond:expr) => (
        if !$cond {
            fail!(concat!("assertion failed: ", stringify!($cond)))
        }
    );
    ($cond:expr, $($arg:expr),+) => (
        if !$cond {
            fail!($($arg),+)
        }
    );
)

/// Ensure that a boolean expression is `true` at runtime.
///
/// This will invoke the `fail!` macro if the provided expression cannot be
/// evaluated to `true` at runtime.
///
/// Unlike `assert!`, `debug_assert!` statements can be disabled by passing
/// `--cfg ndebug` to the compiler. This makes `debug_assert!` useful for
/// checks that are too expensive to be present in a release build but may be
/// helpful during development.
///
/// # Example
///
/// ```
/// // the failure message for these assertions is the stringified value of the
/// // expression given.
/// debug_assert!(true);
/// # fn some_expensive_computation() -> bool { true }
/// debug_assert!(some_expensive_computation());
///
/// // assert with a custom message
/// # let x = true;
/// debug_assert!(x, "x wasn't true!");
/// # let a = 3i; let b = 27i;
/// debug_assert!(a + b == 30, "a = {}, b = {}", a, b);
/// ```
#[macro_export]
macro_rules! debug_assert(
    ($($arg:tt)*) => (if cfg!(not(ndebug)) { assert!($($arg)*); })
)

/// Asserts that two expressions are equal to each other, testing equality in
/// both directions.
///
/// On failure, this macro will print the values of the expressions.
///
/// # Example
///
/// ```
/// let a = 3i;
/// let b = 1i + 2i;
/// assert_eq!(a, b);
/// ```
#[macro_export]
macro_rules! assert_eq(
    ($given:expr , $expected:expr) => ({
        match (&($given), &($expected)) {
            (given_val, expected_val) => {
                // check both directions of equality....
                if !((*given_val == *expected_val) &&
                     (*expected_val == *given_val)) {
                    fail!("assertion failed: `(left == right) && (right == left)` \
                           (left: `{}`, right: `{}`)", *given_val, *expected_val)
                }
            }
        }
    })
)

/// Asserts that two expressions are equal to each other, testing equality in
/// both directions.
///
/// On failure, this macro will print the values of the expressions.
///
/// Unlike `assert_eq!`, `debug_assert_eq!` statements can be disabled by
/// passing `--cfg ndebug` to the compiler. This makes `debug_assert_eq!`
/// useful for checks that are too expensive to be present in a release build
/// but may be helpful during development.
///
/// # Example
///
/// ```
/// let a = 3i;
/// let b = 1i + 2i;
/// debug_assert_eq!(a, b);
/// ```
#[macro_export]
macro_rules! debug_assert_eq(
    ($($arg:tt)*) => (if cfg!(not(ndebug)) { assert_eq!($($arg)*); })
)

// NOTE: remove after the next snapshot
#[cfg(stage0)]
#[macro_export]
macro_rules! try(
    ($e:expr) => (match $e { Ok(e) => e, Err(e) => return Err(e) })
)

/// Helper macro for unwrapping `Result` values while returning early with an
/// error if the value of the expression is `Err`. For more information, see
/// `std::io`.
#[cfg(not(stage0))]
#[macro_export]
macro_rules! try(
    ($e:expr) => (match $e {
        $crate::result::Ok(e) => e,
        $crate::result::Err(e) => return $crate::result::Err(e)
    })
)

/// Use the `format!` syntax to write data into a buffer of type `&mut Writer`.
/// See `std::fmt` for more information.
///
/// # Example
///
/// ```
/// # #![allow(unused_must_use)]
/// use std::io::MemWriter;
///
/// let mut w = MemWriter::new();
/// write!(&mut w, "test");
/// write!(&mut w, "formatted {}", "arguments");
/// ```
#[macro_export]
macro_rules! write(
    ($dst:expr, $($arg:tt)*) => ({
        format_args_method!($dst, write_fmt, $($arg)*)
    })
)

/// Equivalent to the `write!` macro, except that a newline is appended after
/// the message is written.
#[macro_export]
macro_rules! writeln(
    ($dst:expr, $fmt:expr $($arg:tt)*) => (
        write!($dst, concat!($fmt, "\n") $($arg)*)
    )
)
