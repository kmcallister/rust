// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Used by `rustc` when compiling a plugin crate.

use middle::ty;

use syntax::{ast, abi, attr, visit};
use syntax::codemap::Span;
use syntax::visit::Visitor;

struct RegistrarFinder {
    registrars: Vec<(ast::NodeId, Span)> ,
}

impl<'v> Visitor<'v> for RegistrarFinder {
    fn visit_item(&mut self, item: &ast::Item) {
        match item.node {
            ast::ItemFn(..) => {
                if attr::contains_name(item.attrs.as_slice(),
                                       "plugin_registrar") {
                    self.registrars.push((item.id, item.span));
                }
            }
            _ => {}
        }

        visit::walk_item(self, item);
    }
}

/// Find the function marked with `#[plugin_registrar]`, if any.
pub fn find_plugin_registrar(tcx: &ty::ctxt, krate: &ast::Crate) {
    let mut finder = RegistrarFinder { registrars: Vec::new() };
    visit::walk_crate(&mut finder, krate);

    match finder.registrars.len() {
        0 => (),
        1 => {
            let (id, span) = finder.registrars.pop().unwrap();
            tcx.sess.plugin_registrar_fn.set(Some(id));
            typecheck_plugin_registrar(tcx, id, span);
        }
        _ => {
            tcx.sess.err("multiple plugin registration functions found");
            for &(_, span) in finder.registrars.iter() {
                tcx.sess.span_note(span, "one is here");
            }
        }
    }

    tcx.sess.abort_if_errors();
}

/// Typecheck the plugin registrar.
fn typecheck_plugin_registrar(tcx: &ty::ctxt, id: ast::NodeId, span: Span) {
    match ty::get(ty::node_id_to_type(tcx, id)).sty {
        ty::ty_bare_fn(ty::BareFnTy { fn_style: ast::NormalFn, abi: abi::Rust, ref sig }) => {
            match sig.inputs.as_slice() {
                [arg_t] => match ty::get(arg_t).sty {
                    ty::ty_rptr(_, ty::mt { mutbl: ast::MutMutable, ty })
                        if ty_is_registry(tcx, ty) => (),
                    _ => tcx.sess.span_err(span, "plugin registrar arg should be \
                                                  &mut rustc::plugin::Registry"),
                },
                _ => tcx.sess.span_err(span, "plugin registrar should have one argument"),
            }
            match ty::get(sig.output).sty {
                ty::ty_nil => (),
                _ => tcx.sess.span_err(span, "plugin registrar should not return anything"),
            }
        }

        _ => tcx.sess.span_err(span, "plugin registrar should be a normal Rust function"),
    }
}

/// Check if the given type is rustc::plugin::Registry.
fn ty_is_registry(tcx: &ty::ctxt, ty: ty::t) -> bool {
    match ty::get(ty).sty {
        ty::ty_struct(def, ref sub) => {
            if !sub.is_noop() {
                return false;
            }

            // Because users can bind any crate at any name, this check is
            // neither sound nor complete. But it will catch the vast majority
            // of mistakes.
            ty::item_path_str(tcx, def).as_slice() == "rustc::plugin::registry::Registry"
        }
        _ => false,
    }
}
