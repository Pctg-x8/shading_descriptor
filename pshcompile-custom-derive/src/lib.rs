#![recursion_limit="128"]

extern crate proc_macro;
extern crate syn;
#[macro_use] extern crate quote;

use proc_macro::TokenStream;

#[proc_macro_derive(SymbolScope, attributes(SymbolMapReferer))]
pub fn impl_symbol_scope(input: TokenStream) -> TokenStream
{
    let ast: DeriveInput = syn::parse(input).unwrap();
    let ref tyname = ast.ident;
    let referer = ast.attrs.iter().filter_map(|a| match a.interpret_meta()
    {
        Some(syn::Meta::NameValue(syn::MetaNameValue { ident: "SymbolMapReferer", ref lit, .. })) => match *lit
        {
            syn::Lit::Str(ref l) => Some(l.value()),
            syn::Lit::Int(ref n) => Some(n.value().to_string()),
            _ => panic!("`SymbolMapReferer` requires a string literal or an integer literal")
        }
        _ => None
    }).next().unwrap_or("0".to_string());
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
