//! Pattern Resolver

use lambda::NumericRef;
use {Location, GenSource, ConstructorEnvironment};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PaintedIdentifier<'s: 't, 't: 'd, 'd> { Normal(&'d GenSource<'s, 't>), DataConstructor(&'d GenSource<'s, 't>) }
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PaintedPattern<'s: 't, 't: 'd, 'd>
{
    Identifier(PaintedIdentifier<'s, 't, 'd>), Numeric(NumericRef<'s, 't>), Placeholder(&'t Location),
    Apply(PaintedIdentifier<'s, 't, 'd>, Vec<PaintedPattern<'s, 't, 'd>>), Slice(&'t Location, Vec<PaintedPattern<'s, 't, 'd>>),
    Tuple(&'t Location, Vec<PaintedPattern<'s, 't, 'd>>)
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pattern<'s: 't, 't: 'd, 'd> { pub iroot: &'d GenSource<'s, 't>, pub child: Box<PaintedPattern<'s, 't, 'd>> }

// Aggregate Pattern IdentRoot, Paint Data Constructor
impl<'s: 't, 't> GenSource<'s, 't>
{
    fn paint_ctor<'d, CE: ConstructorEnvironment<'s, 't>>(&'d self, cenv: &CE) -> PaintedIdentifier<'s, 't, 'd> where 't: 'd
    {
        cenv.lookup_dctor_index(self.text()).map_or_else(|| PaintedIdentifier::Normal(self), |_| PaintedIdentifier::DataConstructor(self))
    }
}

#[cfg(test)]
mod test
{
    use super::*;

    /*#[test] fn paint_ctor()
    {
        let mut ctors = ::ConstructorEnv::new();
        ctors.dctor_map.insert("TestCtor1".to_owned(), DataConstructorIndex { scope: 0, ctor: 0 });
        ctors.dctor_map.insert("TestCtor2".to_owned(), DataConstructorIndex { scope: 0, ctor: 1 });
        ctors.data.place_back() <- ::TypedDataConstructorScope
        {
            name: ::GenSource::Generated("TestData".to_owned()), ty: ::TyDeformerIntermediate::symref(::GenSource::Generated("t".to_owned())),
            ctors: vec![::TypedDataConstructor
            {
                name: ::GenSource::Generated("TestCtor1".to_owned()),
                param_count: 0, ty: ::TyDeformerIntermediate::symref(::GenSource::Generated("TestData".to_owned())),
                expressed: ::Lambda::Unit(&Location::EMPTY)
            }, ::TypedDataConstructor
            {
                name: ::GenSource::Generated("TestCtor2".to_owned()),
                param_count: 0, ty: ::TyDeformerIntermediate::symref(::GenSource::Generated("TestData".to_owned())),
                expressed: ::Lambda::Unit(&Location::EMPTY)
            }]
        };
        let c1 = ::GenSource::Generated("TestCtor1".to_owned()); assert_eq!(c1.paint_ctor(&ctors), PaintedIdentifier::DataConstructor(&c1));
        let c1 = ::GenSource::Generated("TestCtor2".to_owned()); assert_eq!(c1.paint_ctor(&ctors), PaintedIdentifier::DataConstructor(&c1));
        let c1 = ::GenSource::Generated("TestCtor3".to_owned()); assert_eq!(c1.paint_ctor(&ctors), PaintedIdentifier::Normal(&c1));
    }*/
}
