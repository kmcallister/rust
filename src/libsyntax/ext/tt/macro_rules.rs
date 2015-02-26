// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ast::{self, TokenTree, TtDelimited, TtSequence, TtToken};
use attr;
use codemap::{Span, DUMMY_SP};
use diagnostic::SpanHandler;
use ext::base::{ExtCtxt, MacResult, SyntaxExtension};
use ext::base::{NormalTT, TTMacroExpander};
use ext::tt::macro_parser::{self, Success, Error, Failure};
use fold::{self, Folder};
use parse::lexer::{new_tt_reader, new_tt_reader_with_doc_flag};
use parse::parser::Parser;
use parse::attr::ParserAttr;
use parse::token::{self, Token, FragSpec};
use parse::token::Token::*;
use print::pprust;
use ptr::P;

use util::small_vector::SmallVector;

use std::cell::RefCell;

struct ParserAnyMacro<'a> {
    parser: RefCell<Parser<'a>>,
}

impl<'a> ParserAnyMacro<'a> {
    /// Make sure we don't have any tokens left to parse, so we don't
    /// silently drop anything. `allow_semi` is so that "optional"
    /// semicolons at the end of normal expressions aren't complained
    /// about e.g. the semicolon in `macro_rules! kapow { () => {
    /// panic!(); } }` doesn't get picked up by .parse_expr(), but it's
    /// allowed to be there.
    fn ensure_complete_parse(&self, allow_semi: bool) {
        let mut parser = self.parser.borrow_mut();
        if allow_semi && parser.token == token::Semi {
            parser.bump()
        }
        if parser.token != token::Eof {
            let token_str = parser.this_token_to_string();
            let msg = format!("macro expansion ignores token `{}` and any \
                               following",
                              token_str);
            let span = parser.span;
            parser.span_err(span, &msg[..]);
        }
    }
}

impl<'a> MacResult for ParserAnyMacro<'a> {
    fn make_expr(self: Box<ParserAnyMacro<'a>>) -> Option<P<ast::Expr>> {
        let ret = self.parser.borrow_mut().parse_expr();
        self.ensure_complete_parse(true);
        Some(ret)
    }
    fn make_pat(self: Box<ParserAnyMacro<'a>>) -> Option<P<ast::Pat>> {
        let ret = self.parser.borrow_mut().parse_pat();
        self.ensure_complete_parse(false);
        Some(ret)
    }
    fn make_items(self: Box<ParserAnyMacro<'a>>) -> Option<SmallVector<P<ast::Item>>> {
        let mut ret = SmallVector::zero();
        loop {
            let mut parser = self.parser.borrow_mut();
            // so... do outer attributes attached to the macro invocation
            // just disappear? This question applies to make_methods, as
            // well.
            match parser.parse_item_with_outer_attributes() {
                Some(item) => ret.push(item),
                None => break
            }
        }
        self.ensure_complete_parse(false);
        Some(ret)
    }

    fn make_methods(self: Box<ParserAnyMacro<'a>>) -> Option<SmallVector<P<ast::Method>>> {
        let mut ret = SmallVector::zero();
        loop {
            let mut parser = self.parser.borrow_mut();
            match parser.token {
                token::Eof => break,
                _ => {
                    ret.push(parser.parse_method_with_outer_attributes());
                }
            }
        }
        self.ensure_complete_parse(false);
        Some(ret)
    }

    fn make_stmt(self: Box<ParserAnyMacro<'a>>) -> Option<P<ast::Stmt>> {
        let attrs = self.parser.borrow_mut().parse_outer_attributes();
        let ret = self.parser.borrow_mut().parse_stmt(attrs);
        self.ensure_complete_parse(true);
        Some(ret)
    }
}

struct MacroRulesMacroExpander {
    name: ast::Ident,
    imported_from: Option<ast::Ident>,
    lhses: Vec<TokenTree>,
    rhses: Vec<TokenTree>,
}

impl TTMacroExpander for MacroRulesMacroExpander {
    fn expand<'cx>(&self,
                   cx: &'cx mut ExtCtxt,
                   sp: Span,
                   arg: &[ast::TokenTree])
                   -> Box<MacResult+'cx> {
        generic_extension(cx,
                          sp,
                          self.name,
                          self.imported_from,
                          arg,
                          &self.lhses,
                          &self.rhses)
    }
}

/// Given `lhses` and `rhses`, this is the new macro we create
fn generic_extension<'cx>(cx: &'cx ExtCtxt,
                          sp: Span,
                          name: ast::Ident,
                          imported_from: Option<ast::Ident>,
                          arg: &[ast::TokenTree],
                          lhses: &[TokenTree],
                          rhses: &[TokenTree])
                          -> Box<MacResult+'cx> {
    if cx.trace_macros() {
        println!("{}! {{ {} }}",
                 token::get_ident(name),
                 pprust::tts_to_string(arg));
    }

    // Which arm's failure should we report? (the one furthest along)
    let mut best_fail_spot = DUMMY_SP;
    let mut best_fail_msg = "internal error: ran no matchers".to_string();

    for (i, lhs_tt) in lhses.iter().enumerate() { // try each arm's matchers
        let lhs_tt = match *lhs_tt {
            TtDelimited(_, ref delim) => &delim.tts[..],
            _ => cx.span_fatal(sp, "malformed macro lhs")
        };
        // `None` is because we're not interpolating
        let arg_rdr = new_tt_reader_with_doc_flag(&cx.parse_sess().span_diagnostic,
                                                  None,
                                                  None,
                                                  arg.iter()
                                                     .cloned()
                                                     .collect(),
                                                  true);
        match macro_parser::parse(cx.parse_sess(), cx.cfg(), arg_rdr, lhs_tt) {
            Success(named_matches) => {
                let rhs = match rhses[i] {
                    // ignore delimiters
                    TtDelimited(_, ref delimed) => delimed.tts.clone(),
                    _ => cx.span_fatal(sp, "macro rhs must be delimited"),
                };
                // rhs has holes ( `$id` and `$(...)` that need filled)
                let trncbr = new_tt_reader(&cx.parse_sess().span_diagnostic,
                                           Some(named_matches),
                                           imported_from,
                                           rhs);
                let mut p = Parser::new(cx.parse_sess(), cx.cfg(), box trncbr);
                p.check_unknown_macro_variable();
                // Let the context choose how to interpret the result.
                // Weird, but useful for X-macros.
                return box ParserAnyMacro {
                    parser: RefCell::new(p),
                } as Box<MacResult+'cx>
            }
            Failure(sp, ref msg) => if sp.lo >= best_fail_spot.lo {
                best_fail_spot = sp;
                best_fail_msg = (*msg).clone();
            },
            Error(sp, ref msg) => cx.span_fatal(sp, &msg[..]),
        }
    }
    cx.span_fatal(best_fail_spot, &best_fail_msg[..]);
}

/// Turns a LHS token tree into a matcher.
///
/// This does the `SubstNt` -> `MatchNt` translation.
///
/// FIXME: Give matchers their own AST / token tree type.
struct MatchNtFolder<'a> {
    hdl: &'a SpanHandler,
}

impl<'a> fold::Folder for MatchNtFolder<'a> {
    fn fold_tts(&mut self, tts: &[TokenTree]) -> Vec<TokenTree> {
        macro_rules! bail {
            ($sp:expr, $($msg:expr),*) => {{
                self.hdl.span_err($sp, $($msg),*);
                return vec![];
            }}
        }

        use std::iter::IntoIterator;

        let mut out = Vec::with_capacity(tts.len());
        let mut tt_iter = tts.into_iter();

        loop {
            match tt_iter.next() {
                // Convert `$x : frag_spec` to a `MatchNt`.
                Some(&TtToken(sp1, SubstNt(id, sty))) => match tt_iter.next() {
                    Some(&TtToken(sp2, Colon)) => match tt_iter.next() {
                        Some(&TtToken(sp3, Ident(fid, _))) => match FragSpec::from_ident(fid) {
                            Some(frag) => {
                                // Congrats, you've reached the top of the mountain.
                                // FIXME: Take the union of sp1 - sp3.
                                out.push(TtToken(sp1, MatchNt(id, sty, frag)));
                            }
                            None => {
                                self.hdl.span_err(sp3, "expected macro fragment specifier");
                                self.hdl.span_help(sp3, FragSpec::help());
                                return vec![];
                            }
                        },
                        _ => bail!(sp2, "expected macro fragment specifier after `:`"),
                    },
                    _ => bail!(sp1, "expected `:` after macro metavariable in matcher"),
                },

                Some(tt) => out.push(fold::noop_fold_tt(tt, self)),

                None => break,
            }
        }

        debug!("MatchNtFolder: old: {:?}", tts);
        debug!("MatchNtFolder: new: {:?}", out);

        out
    }
}

pub fn parse_body(hdl: &SpanHandler, span: Span, body: Vec<TokenTree>)
    -> Option<(Vec<TokenTree>, Vec<TokenTree>)>
{
    let end_span = Span {
        lo: span.hi,
        hi: span.hi,
        expn_id: span.expn_id
    };

    let mut tts = body.into_iter();
    let mut lhses = vec![];
    let mut rhses = vec![];

    let mut make_matcher = MatchNtFolder {
        hdl: hdl,
    };

    // Parse the macro as a sequence of rules.
    loop {
        match tts.next() {
            Some(lhs) => lhses.push(make_matcher.fold_tt(&lhs)),
            None => break,
        }

        match tts.next() {
            Some(TtToken(_, FatArrow)) => (),
            Some(tt) => {
                hdl.span_err(tt.get_span(), &format!("expected `=>`, found `{}`",
                                                    &pprust::tt_to_string(&tt)));
                return None;
            }
            None => {
                hdl.span_err(end_span, "expected `=>`, found end of macro");
                return None;
            }
        }

        match tts.next() {
            Some(rhs) => rhses.push(rhs),
            None => {
                hdl.span_err(end_span, "expected right-hand side, found end of macro");
                return None;
            }
        }

        match tts.next() {
            None => break,
            Some(TtToken(_, Semi)) => (),
            Some(tt) => {
                hdl.span_err(tt.get_span(), &format!("expected macro rule or end of macro,
                                                     found `{}`", &pprust::tt_to_string(&tt)));
                return None;
            }
        }
    }

    Some((lhses, rhses))
}

/// Parse a `macro_rules!` invocation into a `MacroDef`.
///
/// If the macro is malformed, emits error(s) and returns `None`.
pub fn parse(cx: &mut ExtCtxt,
             it: &ast::Item,
             body: Vec<TokenTree>) -> Option<ast::MacroDef>
{
    let (lhses, rhses) = match parse_body(&cx.parse_sess.span_diagnostic, it.span, body) {
        None => return None,
        Some((l, r)) => (l, r),
    };

    for lhs in &lhses {
        check_lhs_nt_follows(cx, lhs, it.span);
    }

    Some(ast::MacroDef {
        ident: it.ident,
        attrs: it.attrs.clone(),
        id: ast::DUMMY_NODE_ID,
        span: it.span,
        imported_from: None,
        export: attr::contains_name(&it.attrs, "macro_export"),
        use_locally: true,
        lhses: lhses,
        rhses: rhses,
    })
}

/// Converts a macro definition invocation into a syntax extension.
pub fn compile(def: &ast::MacroDef) -> SyntaxExtension {
    let exp = box MacroRulesMacroExpander {
        name: def.ident,
        imported_from: def.imported_from,
        lhses: def.lhses.clone(),
        rhses: def.rhses.clone(),
    };
    NormalTT(exp, Some(def.span))
}

fn check_lhs_nt_follows(cx: &mut ExtCtxt, lhs: &TokenTree, sp: Span) {
    // lhs is going to be like TtDelimited(...), where the entire lhs is
    // those tts. Or, it can be a "bare sequence", not wrapped in parens.
    match lhs {
        &TtDelimited(_, ref tts) => {
            check_matcher(cx, tts.tts.iter(), &Eof);
        }
        tt @ &TtSequence(..) => {
            check_matcher(cx, Some(tt).into_iter(), &Eof);
        }
        _ => cx.span_bug(sp, "wrong-structured lhs for follow check (didn't find \
                              a TtDelimited or TtSequence)"),
    }
    // we don't abort on errors on rejection, the driver will do that for us
    // after parsing/expansion. we can report every error in every macro this way.
}

// returns the last token that was checked, for TtSequence. this gets used later on.
fn check_matcher<'a, I>(cx: &mut ExtCtxt, matcher: I, follow: &Token)
-> Option<(Span, Token)> where I: Iterator<Item=&'a TokenTree> {
    let mut last = None;

    // 2. For each token T in M:
    let mut tokens = matcher.peekable();
    while let Some(token) = tokens.next() {
        last = match *token {
            TtToken(sp, MatchNt(ref name, _, frag_spec)) => {
                // ii. If T is a simple NT, look ahead to the next token T' in
                // M.
                let next_token = match tokens.peek() {
                    // If T' closes a complex NT, replace T' with F
                    Some(&&TtToken(_, CloseDelim(_))) => follow.clone(),
                    Some(&&TtToken(_, ref tok)) => tok.clone(),
                    Some(&&TtSequence(sp, _)) => {
                        cx.span_err(sp,
                                    &format!("`${0}:{1}` is followed by a \
                                              sequence repetition, which is not \
                                              allowed for `{1}` fragments",
                                             name.as_str(), frag_spec.as_str())
                                        );
                        Eof
                    },
                    // die next iteration
                    Some(&&TtDelimited(_, ref delim)) => delim.close_token(),
                    // else, we're at the end of the macro or sequence
                    None => follow.clone()
                };

                let tok = if let TtToken(_, ref tok) = *token { tok } else { unreachable!() };
                // If T' is in the set FOLLOW(NT), continue. Else, reject.
                match (&next_token, is_in_follow(cx, &next_token, frag_spec)) {
                    (&Eof, _) => return Some((sp, tok.clone())),
                    (_, true) => continue,
                    (next, false) => {
                        cx.span_err(sp, &format!("`${0}:{1}` is followed by `{2}`, which \
                                                  is not allowed for `{1}` fragments",
                                                 name.as_str(), frag_spec.as_str(),
                                                 pprust::token_to_string(next)));
                        continue
                    },
                }
            },
            TtSequence(sp, ref seq) => {
                // iii. Else, T is a complex NT.
                match seq.separator {
                    // If T has the form $(...)U+ or $(...)U* for some token U,
                    // run the algorithm on the contents with F set to U. If it
                    // accepts, continue, else, reject.
                    Some(ref u) => {
                        let last = check_matcher(cx, seq.tts.iter(), u);
                        match last {
                            // Since the delimiter isn't required after the last
                            // repetition, make sure that the *next* token is
                            // sane. This doesn't actually compute the FIRST of
                            // the rest of the matcher yet, it only considers
                            // single tokens and simple NTs. This is imprecise,
                            // but conservatively correct.
                            Some((span, tok)) => {
                                let fol = match tokens.peek() {
                                    Some(&&TtToken(_, ref tok)) => tok.clone(),
                                    Some(&&TtDelimited(_, ref delim)) => delim.close_token(),
                                    Some(_) => {
                                        cx.span_err(sp, "sequence repetition followed by \
                                                another sequence repetition, which is not allowed");
                                        Eof
                                    },
                                    None => Eof
                                };
                                check_matcher(cx, Some(&TtToken(span, tok.clone())).into_iter(),
                                              &fol)
                            },
                            None => last,
                        }
                    },
                    // If T has the form $(...)+ or $(...)*, run the algorithm
                    // on the contents with F set to the token following the
                    // sequence. If it accepts, continue, else, reject.
                    None => {
                        let fol = match tokens.peek() {
                            Some(&&TtToken(_, ref tok)) => tok.clone(),
                            Some(&&TtDelimited(_, ref delim)) => delim.close_token(),
                            Some(_) => {
                                cx.span_err(sp, "sequence repetition followed by another \
                                             sequence repetition, which is not allowed");
                                Eof
                            },
                            None => Eof
                        };
                        check_matcher(cx, seq.tts.iter(), &fol)
                    }
                }
            },
            TtToken(..) => {
                // i. If T is not an NT, continue.
                continue
            },
            TtDelimited(_, ref tts) => {
                // if we don't pass in that close delimiter, we'll incorrectly consider the matcher
                // `{ $foo:ty }` as having a follow that isn't `RBrace`
                check_matcher(cx, tts.tts.iter(), &tts.close_token())
            }
        }
    }
    last
}

fn is_in_follow(_: &ExtCtxt, tok: &Token, frag: FragSpec) -> bool {
    if let &CloseDelim(_) = tok {
        return true;
    }

    match frag {
        FragSpec::Item => {
            // since items *must* be followed by either a `;` or a `}`, we can
            // accept anything after them
            true
        },
        FragSpec::Block => {
            // anything can follow block, the braces provide a easy boundary to
            // maintain
            true
        },
        FragSpec::Stmt | FragSpec::Expr  => {
            match *tok {
                FatArrow | Comma | Semi => true,
                _ => false
            }
        },
        FragSpec::Pat => {
            match *tok {
                FatArrow | Comma | Eq => true,
                _ => false
            }
        },
        FragSpec::Path | FragSpec::Ty => {
            match *tok {
                Comma | FatArrow | Colon | Eq | Gt => true,
                Ident(i, _) if i.as_str() == "as" => true,
                _ => false
            }
        },
        FragSpec::Ident => {
            // being a single token, idents are harmless
            true
        },
        FragSpec::Meta | FragSpec::Tt => {
            // being either a single token or a delimited sequence, tt is
            // harmless
            true
        },
    }
}
