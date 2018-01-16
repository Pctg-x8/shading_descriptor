extern crate proc_macro;
extern crate syn;
#[macro_use] extern crate quote;

use proc_macro::TokenStream;

#[proc_macro_derive(SymbolScope)]
pub fn impl_symbol_scope(input: TokenStream) -> TokenStream
{
    let s = input.to_string();
    let ast = syn::parse_derive_input(&s).unwrap();
    let ref tyname = ast.ident;
    let gen = quote!{
        impl<'s: 't, 't> ::symbol::SymbolScope<'s, 't> for #tyname<'s, 't>
        {
            fn symbol_map(&self) -> &::std::collections::HashMap<::std::borrow::Cow<'t, str>, ::symbol::SymbolKind<'s, 't>>
            {
                &self.0
            }
            fn symbol_map_mut(&mut self) -> &mut ::std::collections::HashMap<::std::borrow::Cow<'t, str>, ::symbol::SymbolKind<'s, 't>>
            {
                &mut self.0
            }
        }
    };
    gen.parse().unwrap()
}
