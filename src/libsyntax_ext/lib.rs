// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Syntax extensions in the Rust compiler.

#![crate_name = "syntax_ext"]
#![unstable(feature = "rustc_private", issue = "27812")]
#![crate_type = "dylib"]
#![crate_type = "rlib"]
#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk-v2.png",
       html_favicon_url = "https://doc.rust-lang.org/favicon.ico",
       html_root_url = "https://doc.rust-lang.org/nightly/")]
#![deny(warnings)]

#![feature(proc_macro_internals)]
#![feature(rustc_private)]
#![feature(staged_api)]

extern crate fmt_macros;
extern crate log;
#[macro_use]
extern crate syntax;
extern crate syntax_pos;
extern crate proc_macro;
extern crate rustc_errors as errors;

mod asm;
mod cfg;
mod concat;
mod concat_idents;
mod env;
mod format;
mod format_foreign;
mod log_syntax;
mod trace_macros;

pub mod proc_macro_registrar;

// for custom_derive
pub mod deriving;

pub mod proc_macro_impl;

use std::rc::Rc;
use syntax::ast;
use syntax::ext::base::{MacroExpanderFn, NormalTT, TTMacroExpander, NamedSyntaxExtension};
use syntax::ext::quote::QuoteMacroExpander;
use syntax::symbol::Symbol;

pub fn register_builtins(resolver: &mut syntax::ext::base::Resolver,
                         user_exts: Vec<NamedSyntaxExtension>,
                         enable_quotes: bool) {
    deriving::register_builtin_derives(resolver);

    let mut register = |name, ext| {
        resolver.add_builtin(ast::Ident::with_empty_ctxt(name), Rc::new(ext));
    };

    macro_rules! register {
        ($( $name:ident: $f:expr, )*) => { $(
            register(Symbol::intern(stringify!($name)),
                     NormalTT(Box::new($f) as Box<TTMacroExpander>, None, false));
        )* }
    }

    if enable_quotes {
        register! {
            // quote_matcher: QuoteMacroExpander::Matcher,
            quote_tokens: QuoteMacroExpander::Tokens,
            quote_expr: QuoteMacroExpander::Expr,
            quote_ty: QuoteMacroExpander::Item,
            quote_item: QuoteMacroExpander::Pat,
            quote_pat: QuoteMacroExpander::Arm,
            quote_arm: QuoteMacroExpander::Ty,
            quote_stmt: QuoteMacroExpander::Stmt,
            quote_attr: QuoteMacroExpander::Attr,
            quote_arg: QuoteMacroExpander::Arg,
            quote_block: QuoteMacroExpander::Block,
            quote_meta_item: QuoteMacroExpander::MetaItem,
            quote_path: QuoteMacroExpander::Path,
        }
    }

    use syntax::ext::source_util::*;
    register! {
        line: expand_line,
        column: expand_column,
        file: expand_file,
        stringify: expand_stringify,
        include: expand_include,
        include_str: expand_include_str,
        include_bytes: expand_include_bytes,
        module_path: expand_mod,

        asm: asm::expand_asm,
        cfg: cfg::expand_cfg,
        concat: concat::expand_syntax_ext,
        concat_idents: concat_idents::expand_syntax_ext,
        env: env::expand_env,
        option_env: env::expand_option_env,
        log_syntax: log_syntax::expand_syntax_ext,
        trace_macros: trace_macros::expand_trace_macros,
    }

    // format_args uses `unstable` things internally.
    register(Symbol::intern("format_args"),
             NormalTT(Box::new(format::expand_format_args), None, true));

    for (name, ext) in user_exts {
        register(name, ext);
    }
}
