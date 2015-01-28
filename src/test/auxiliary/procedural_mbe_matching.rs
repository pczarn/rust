// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// force-host

#![crate_type="dylib"]
#![feature(plugin_registrar)]

extern crate syntax;
extern crate rustc;

use syntax::codemap::Span;
use syntax::parse::token;
use syntax::ast::{TokenTree, TtToken};
use syntax::ext::base::{ExtCtxt, MacResult, DummyResult, MacExpr};
use rustc::plugin::Registry;

fn expand_mbe_matching(cx: &mut ExtCtxt, sp: Span, args: &[TokenTree])
        -> Box<MacResult + 'static> {

    let doc_text = quote_attr!(cx, #[doc = " text "]);

    let matcher = quote_matcher!(cx, start #[$doc1:meta] a #[doc = " text "] b);
    let tt = quote_tokens!(cx,
        start
        /// foo
        a $doc_text b
    );

    match TokenTree::parse(&matcher[], cx, &tt[]) {
        Success(map) => {
            assert_eq!(1, map.len());
            match map.get(&token::str_to_ident("doc1")) {
                Some(&MatchedNonterminal(NtMeta(_))) => {}
                _ => panic!()
            }
        }
        Failure(_, s) | Error(_, s) => {
            panic!("expected Success, but got Error/Failure: {}", s);
        }
    }


    let overly_complicated = quote_matcher!(cx, $fnname:ident, $arg:ident, $ty:ty, $body:block,
                                                $val:expr, $pat:pat, $res:path);
    let tt = quote_tokens!(cx, abc, d, Fn(T)->U, { block }, 2 + 3, Some(xyz), ::path::somewhere);

    match TokenTree::parse(&overly_complicated[], cx, &tt[]) {
        Success(map) => {
            assert_eq!(7, map.len());
            match map.get(&token::str_to_ident("ty")) {
                Some(&MatchedNonterminal(NtTy(_))) => {}
                _ => panic!()
            }
        }
        Failure(_, s) | Error(_, s) => {
            panic!("expected Success, but got Error/Failure: {}", s);
        }
    }

    let matcher = quote_matcher!(cx, $($e:expr);*);

    let mac_expr = match TokenTree::parse(&matcher[], cx, args) {
        Success(map) => {
            match map.get(&token::str_to_ident("e")) {
                Some(&MatchedSeq(exprs)) => {
                    assert_eq!(1, exprs.len());
                    match *exprs[0] {
                        MatchedNonterminal(NtExpr(mac_expr)) => {
                            mac_expr
                        }
                        _ => panic!()

                    }
                }
                _ => panic!()
            }
        }
        Failure(_, s) | Error(_, s) => {
            panic!("expected Success, but got Error/Failure: {}", s);
        }
    };

    MacExpr::new(mac_expr)
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("mbe_matching", expand_mbe_matching);
}
