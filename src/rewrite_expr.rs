// Expression Rewriter/Simplizer

use {parser, deformer};
use {Deformable, DeformationError};
use {Location, Semantics, BType, GenSource, Source, GenNumeric};
use deformer::SymPath;
use std::collections::HashMap;
use std::borrow::Cow;

pub struct PipelineDeformed<'s: 't, 't>
{
    pub ast: &'t parser::ShadingPipeline<'s>, pub bindings: BoundMap<'s, 't>,
    pub vsh: Option<StageDeformed<'s, 't>>, pub fsh: Option<StageDeformed<'s, 't>>, pub gsh: Option<StageDeformed<'s, 't>>,
    pub hsh: Option<StageDeformed<'s, 't>>, pub dsh: Option<StageDeformed<'s, 't>>
}
pub struct StageDeformed<'s: 't, 't>
{
    pub ast: &'t parser::ShaderStageDefinition<'s>, pub bindings: BoundMap<'s, 't>, pub io: IOSemanticsMap<'s, 't>
}
pub struct ConstantDef<'s: 't, 't>
{
    pub type_hint: Option<deformer::FullTy<'s, 't>>, pub default_expr: Option<deformer::Expr<'s, 't>>
}
pub enum BindingTree<'s: 't, 't>
{
    /// x...
    Expr(deformer::Expr<'s, 't>),
    /// \<pat>. x...
    WithArgument(deformer::ExprPat<'s, 't>, Box<BindingTree<'s, 't>>)
}
pub struct Binding<'s: 't, 't> { pub type_hint: Option<deformer::FullTy<'s, 't>>, pub tree: BindingTree<'s, 't> }

#[derive(Debug, Clone, Copy, PartialEq, Eq)] pub enum RegisterResult { Success, Exists }

pub struct IOSemanticsMap<'s: 't, 't>
{
    pub inputs: HashMap<Semantics, (&'s str, BType)>,
    pub outputs: HashMap<Semantics, (&'s str, Option<BType>, deformer::Expr<'s, 't>)>
}
pub struct BoundMap<'s: 't, 't>
{
    pub uniforms: HashMap<&'s str, deformer::FullTy<'s, 't>>,
    pub constants: HashMap<&'s str, ConstantDef<'s, 't>>,
    pub defs: HashMap<Cow<'s, str>, Vec<Binding<'s, 't>>>,
}
impl<'s: 't, 't> IOSemanticsMap<'s, 't>
{
    fn new() -> Self { IOSemanticsMap { inputs: HashMap::new(), outputs: HashMap::new() } }
    fn register_input(&mut self, sem: Semantics, name: &'s str, type_: BType) -> RegisterResult
    {
        if self.inputs.contains_key(&sem) { RegisterResult::Exists }
        else { self.inputs.insert(sem, (name, type_)); RegisterResult::Success }
    }
    fn register_output(&mut self, sem: Semantics, name: &'s str, type_hint: Option<BType>, expr: deformer::Expr<'s, 't>) -> RegisterResult
    {
        if self.outputs.contains_key(&sem) { RegisterResult::Exists }
        else { self.outputs.insert(sem, (name, type_hint, expr)); RegisterResult::Success }
    }
}
impl<'s: 't, 't> BoundMap<'s, 't>
{
    fn new() -> Self { BoundMap { uniforms: HashMap::new(), constants: HashMap::new(), defs: HashMap::new() } }
    fn register_uniform(&mut self, name: &'s str, type_: deformer::FullTy<'s, 't>) -> RegisterResult
    {
        if self.uniforms.contains_key(name) { RegisterResult::Exists }
        else { self.uniforms.insert(name, type_); RegisterResult::Success }
    }
    fn register_constant(&mut self, name: &'s str, details: ConstantDef<'s, 't>) -> RegisterResult
    {
        if self.constants.contains_key(name) { RegisterResult::Exists }
        else { self.constants.insert(name, details); RegisterResult::Success }
    }
    fn register<N: Into<Cow<'s, str>>>(&mut self, name: N, tree: Binding<'s, 't>)
    {
        self.defs.entry(name.into()).or_insert_with(Vec::new).push(tree);
    }
}

static NTH_TUPLE: Source<'static> = Source { slice: "nth_tuple", pos: Location::EMPTY };

impl<'s> parser::ShaderStageDefinition<'s>
{
    pub fn deform<'t>(&'t self) -> Result<StageDeformed<'s, 't>, Vec<ComplexDeformationError<'s>>> where 's: 't
    {
        let mut errors = Vec::new();
        let (mut io, mut bindings) = (IOSemanticsMap::new(), BoundMap::new());
        let ref assoc = self.assoc.borrow();
        
        for (name, si) in self.inputs.iter().filter_map(|si| si.name.map(|n| (n, si)))
        {
            if io.register_input(si.semantics, name, si._type) == RegisterResult::Exists
            {
                errors.place_back() <- ComplexDeformationError::SemanticsConflict(si.semantics, si.location.clone());
            }
        }
        for (name, so) in self.outputs.iter().filter_map(|so| so.name.map(|n| (n, so)))
        {
            let expr = CollectErrors!(so.expr.deform(assoc) =>? errors; continue);
            if io.register_output(so.semantics, name, so._type.clone(), expr) == RegisterResult::Exists
            {
                errors.place_back() <- ComplexDeformationError::SemanticsConflict(so.semantics, so.location.clone());
            }
        }
        for (name, c) in self.constants.iter().filter_map(|c| c.name.map(|n| (n, c)))
        {
            let type_hint = CollectErrors!(opt c._type.as_ref().map(|x| x.deform(assoc)) =>? errors; continue);
            let default_expr = CollectErrors!(opt c.value.as_ref().map(|x| x.deform(assoc)) =>? errors; continue);
            if bindings.register_constant(name, ConstantDef { type_hint, default_expr }) == RegisterResult::Exists
            {
                errors.place_back() <- ComplexDeformationError::ConstantNameConflict(name, c.location.clone());
            }
        }
        for (name, u) in self.uniforms.iter().filter_map(|u| u.name.map(|n| (n, u)))
        {
            let type_ = CollectErrors!(u._type.deform(assoc) =>? errors; continue);
            if bindings.register_uniform(name, type_) == RegisterResult::Exists
            {
                errors.place_back() <- ComplexDeformationError::UniformNameConflict(name, u.location.clone());
            }
        }
        for v in &self.values
        {
            let mut lhs = CollectErrors!(v.pat.deform(assoc) =>? errors; continue);
            let mut rhs = BindingTree::Expr(CollectErrors!(v.value.deform(assoc) =>? errors; continue));
            let type_hint = CollectErrors!(opt v._type.as_ref().map(|x| x.deform(assoc)) =>? errors; continue);

            fn boundable<'s: 't, 't, 'd>(t: &'d deformer::ExprPat<'s, 't>) -> Result<Option<&'d GenSource<'s, 't>>, &'d Location>
            {
                match *t
                {
                    deformer::ExprPat::SymBinding(ref s) => Ok(Some(s)),
                    deformer::ExprPat::Placeholder(_) => Ok(None),
                    _ => Err(t.position())
                }
            }
            match lhs
            {
                // tuple pattern: (a, b) = f x => #tup_(a,b) = f x; a = first #tup_(a,b); b = second #tup_(a,b)
                deformer::ExprPat::Tuple(t0, ts) =>
                {
                    let (b0, bs) = (boundable(&t0), ts.iter().map(boundable).collect::<Result<Vec<_>, _>>());
                    if let Err(p) = b0 { errors.place_back() <- ComplexDeformationError::Unboundable(p.clone()); }
                    if let Err(p) = bs { errors.place_back() <- ComplexDeformationError::Unboundable(p.clone()); }
                    if b0.is_err() || bs.is_err() { continue; }
                    let (b0, bs) = (b0.unwrap(), bs.unwrap());
                    let decons_name =
                        format!("#tup_({},{})", b0.map_or("_", |x| x.text()), bs.iter().map(|b| b.map_or("_", |x| x.text())).collect::<Vec<&str>>().join(","));
                    bindings.register(decons_name.clone(), Binding { type_hint, tree: rhs });
                    let decons_t = deformer::Expr::Apply(GenSource::Generated(decons_name), Vec::new());
                    if let Some(b0) = b0
                    {
                        let index = deformer::Expr::Numeric(GenNumeric::from(0));
                        bindings.register(b0.text().to_owned(), Binding
                        {
                            type_hint: None, tree: BindingTree::Expr(deformer::Expr::Apply(GenSource::from(&NTH_TUPLE), vec![index, decons_t.clone()]))
                        });
                    }
                    for (i, n) in bs.iter().enumerate().filter_map(|(i, n)| n.map(|n| (i, n)))
                    {
                        let index = deformer::Expr::Numeric(GenNumeric::from(i as u64 + 1));
                        bindings.register(n.text().to_owned(), Binding
                        {
                            type_hint: None, tree: BindingTree::Expr(deformer::Expr::Apply(GenSource::from(&NTH_TUPLE), vec![index, decons_t.clone()]))
                        });
                    }
                },
                // simple applying pattern: a n = n + 2 => a = \n. n + 2
                deformer::ExprPat::Apply(SymPath { base, desc }, args) => if desc.is_empty()
                {
                    let rhs = args.into_iter().rev().fold(rhs, |r, a| BindingTree::WithArgument(a, box r));
                    bindings.register(base.text().to_owned(), Binding { type_hint, tree: rhs });
                }
                else { errors.place_back() <- ComplexDeformationError::Unboundable(base.position().clone()); },
                // simple binding pattern: a = 2
                // deformer::ExprPat::SymBinding(name) => { bindings.register(name.text(), Binding { type_hint, tree: rhs }); },
                _ => { errors.place_back() <- ComplexDeformationError::Unboundable(lhs.position().clone()); }
            }
        }

        if errors.is_empty() { Ok(StageDeformed { ast: self, bindings, io }) } else { Err(errors) }
    }
}

pub enum ComplexDeformationError<'s>
{
    Inherit(DeformationError), SemanticsConflict(Semantics, Location),
    ConstantNameConflict(&'s str, Location), UniformNameConflict(&'s str, Location),
    Unboundable(Location)
}
impl<'s> From<DeformationError> for ComplexDeformationError<'s> { fn from(v: DeformationError) -> Self { ComplexDeformationError::Inherit(v) } }
