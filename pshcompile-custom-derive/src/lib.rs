#![recursion_limit="128"]

extern crate proc_macro;
extern crate syn;
#[macro_use] extern crate quote;

use proc_macro::TokenStream;
use syn::{MetaItem, Lit};

#[proc_macro_derive(SymbolScope, attributes(SymbolMapReferer))]
pub fn impl_symbol_scope(input: TokenStream) -> TokenStream
{
    let s = input.to_string();
    let ast = syn::parse_derive_input(&s).unwrap();
    let referer = ast.attrs.iter().filter_map(|a| match a.value
    {
        MetaItem::NameValue(ref ident, ref lit) if ident == "SymbolMapReferer" => match *lit
        {
            Lit::Str(ref l, _) => Some(l.to_owned()), Lit::Int(n, _) => Some(n.to_string()),
            _ => panic!("`SymbolMapReferer` requires a string literal or an integer literal")
        }
        _ => None
    }).next().unwrap_or("0".to_string());
    let ref tyname = ast.ident;
    let gen = quote!{
        impl<'s: 't, 't> ::symbol::SymbolScope<'s, 't> for #tyname<'s, 't>
        {
            fn symbol_map(&self) -> &::std::collections::HashMap<::std::borrow::Cow<'t, str>, ::symbol::SymbolKind<'s, 't>>
            {
                &self.#referer
            }
            fn symbol_map_mut(&mut self) -> &mut ::std::collections::HashMap<::std::borrow::Cow<'t, str>, ::symbol::SymbolKind<'s, 't>>
            {
                &mut self.#referer
            }
        }
    };
    gen.parse().unwrap()
}
