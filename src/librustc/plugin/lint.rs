// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::lint;

use syntax::visit::Visitor;
use syntax::codemap::Span;
use std::mem;

#[allow(raw_pointer_deriving)]
#[deriving(Clone)]
pub struct Context {
    inner: *mut lint::Context<'static>,
}

impl Context {
    #[doc(hidden)]
    pub fn new<'a>(inner: &mut lint::Context<'a>) -> Context {
        Context {
            inner: unsafe { mem::transmute(inner as *mut lint::Context<'a>) },
        }
    }

    pub fn warn(&self, span: Span, msg: &str) {
        unsafe {
            (*self.inner).span_lint(lint::LintPlugin, span, msg);
        }
    }
}

pub type Lint = Box<Visitor<Context>>;
