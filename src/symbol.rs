//! Symbol Collector

use {parser, deformer};
use {Location, GenSource, Source, Lambda};
use std::collections::HashMap;
use std::borrow::{Borrow, Cow};
use std::hash::Hash;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataConstructor<'s: 't, 't>
{
    pub name: GenSource<'s, 't>, pub ty: deformer::Ty<'s, 't>, pub expressed: Lambda<'s, 't>
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataConstructorScope<'s: 't, 't>
{
    pub name: GenSource<'s, 't>, pub ty_expressed: deformer::Ty<'s, 't>, pub ctors: Vec<DataConstructor<'s, 't>>
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolKind<'s: 't, 't> { Value(GenSource<'s, 't>), Type(GenSource<'s, 't>), Data(DataConstructorScope<'s, 't>) }
impl<'s: 't, 't> SymbolKind<'s, 't>
{
    pub fn kind_text(&self) -> &'static str
    {
        match *self
        {
            SymbolKind::Value(_) => "Value", SymbolKind::Type(_) => "Type", SymbolKind::Data(_) => "Data"
        }
    }
    pub fn position(&self) -> &Location
    {
        match *self
        {
            SymbolKind::Value(ref s) => s.position(), SymbolKind::Type(ref s) => s.position(),
            SymbolKind::Data(ref d) => d.name.position()
        }
    }
}
// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct SymbolScope<'s: 't, 't>(HashMap<Cow<'t, str>, SymbolKind<'s, 't>>);
pub trait SymbolScope<'s: 't, 't>
{
    fn symbol_map(&self) -> &HashMap<Cow<'t, str>, SymbolKind<'s, 't>>;
    fn symbol_map_mut(&mut self) -> &mut HashMap<Cow<'t, str>, SymbolKind<'s, 't>>;

    fn register_value<N: Hash + Eq + ?Sized>(&mut self, name: &'t N, span: GenSource<'s, 't>) -> Result<(), &SymbolKind<'s, 't>>
        where Cow<'t, str>: Borrow<N> + From<&'t N>, &'t N: Into<Cow<'t, str>>
    {
        if self.symbol_map().contains_key(&name) { Err(self.symbol_map().get(&name).unwrap()) }
        else { self.symbol_map_mut().insert(name.into(), SymbolKind::Value(span)); Ok(()) }
    }
    fn register_type<N: Into<Cow<'t, str>> + Hash + Eq>(&mut self, name: N, span: GenSource<'s, 't>) -> Result<(), &SymbolKind<'s, 't>>
        where Cow<'t, str>: Borrow<N>
    {
        if self.symbol_map().contains_key(&name) { Err(self.symbol_map().get(&name).unwrap()) }
        else { self.symbol_map_mut().insert(name.into(), SymbolKind::Type(span)); Ok(()) }
    }
    fn register_data<N: Into<Cow<'t, str>> + Hash + Eq>(&mut self, name: N, scope: DataConstructorScope<'s, 't>) -> Result<(), &SymbolKind<'s, 't>>
        where Cow<'t, str>: Borrow<N>
    {
        if self.symbol_map().contains_key(&name) { Err(self.symbol_map().get(&name).unwrap()) }
        else { self.symbol_map_mut().insert(name.into(), SymbolKind::Data(scope)); Ok(()) }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, SymbolScope)] #[SymbolMapReferer = "map"]
pub struct PipelineSymbols<'s: 't, 't>
{
    pub map: HashMap<Cow<'t, str>, SymbolKind<'s, 't>>,
    pub vsh: Option<ShaderStageSymbols<'s, 't>>, pub hsh: Option<ShaderStageSymbols<'s, 't>>,
    pub dsh: Option<ShaderStageSymbols<'s, 't>>, pub gsh: Option<ShaderStageSymbols<'s, 't>>,
    pub fsh: Option<ShaderStageSymbols<'s, 't>>
}
#[derive(Debug, Clone, PartialEq, Eq, SymbolScope)]
pub struct ShaderStageSymbols<'s: 't, 't>(HashMap<Cow<'t, str>, SymbolKind<'s, 't>>);
impl<'s: 't, 't> PipelineSymbols<'s, 't>
{
    pub fn new() -> Self { PipelineSymbols { map: HashMap::new(), vsh: None, hsh: None, dsh: None, gsh: None, fsh: None } }
}
impl<'s: 't, 't> ShaderStageSymbols<'s, 't>
{
    pub fn new() -> Self { ShaderStageSymbols(HashMap::new()) }
}

pub struct SymbolDuplicateError<'s: 't, 't> { pub org_pos: Location, pub pos: &'t Location, pub name: &'s str, pub org_kind: &'static str }
impl<'s: 't, 't> ::std::fmt::Display for SymbolDuplicateError<'s, 't>
{
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result
    {
        write!(fmt, "Symbol \"{}\"(at {}) has already registered as {}(at {})", self.name, self.pos, self.org_kind, self.org_pos)
    }
}

pub trait SymbolCollector<'s: 't, 't>
{
    type Map: 't;
    fn collect_symbols(&'t self) -> Result<Self::Map, Vec<SymbolDuplicateError<'s, 't>>>;
}
impl<'s: 't, 't> SymbolCollector<'s, 't> for parser::ShaderStageDefinition<'s>
{
    type Map = ShaderStageSymbols<'s, 't>;
    fn collect_symbols(&'t self) -> Result<Self::Map, Vec<SymbolDuplicateError<'s, 't>>>
    {
        let (mut symbols, mut errors) = (ShaderStageSymbols::new(), Vec::new());
        for (name, location) in
            self.constants.iter().filter_map(|c| c.name.map(|n| (n, &c.location)))
            .chain(self.uniforms.iter().filter_map(|u| u.name.map(|n| (n, &u.location))))
            .chain(self.inputs.iter().filter_map(|i| i.name.map(|n| (n, &i.location))))
            .chain(self.outputs.iter().filter_map(|o| o.name.map(|n| (n, &o.location))))
        {
            if let Err(e) = symbols.register_value(name, GenSource::GeneratedSlice(Source { slice: name, pos: location.clone() }))
            {
                errors.place_back() <- SymbolDuplicateError { pos: location, name, org_kind: e.kind_text(), org_pos: e.position().clone() };
            }
        }
        for v in &self.values
        {

        }
        if errors.is_empty() { Ok(symbols) } else { Err(errors) }
    }
}
