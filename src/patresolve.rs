//! Pattern Resolver

use deformer::GenSource;
use lambda::NumericRef;
use {Location, DeformedExprPat, ConstructorEnvironment};

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
        cenv.lookup_dctor(self.text()).map_or_else(|| PaintedIdentifier::Normal(self), |_| PaintedIdentifier::DataConstructor(self))
    }
}
