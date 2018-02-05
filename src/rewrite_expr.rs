// Expression Rewriter/Simplizer

use {parser, deformer, Position};
use {Deformable, DeformationError};
use {Location, Semantics, BType, GenSource, Source, GenNumeric};
use deformer::SymPath;
use std::collections::HashMap;
use std::borrow::Cow;
use parser::{AssociativityEnv, AssociativityEnvironment};

#[derive(Debug)]
pub struct PipelineDeformed<'t>
{
    pub bindings: BoundMap<'t>, pub types: DeformedTypes<'t>,
    pub vsh: Option<StageDeformed<'t>>, pub fsh: Option<StageDeformed<'t>>, pub gsh: Option<StageDeformed<'t>>,
    pub hsh: Option<StageDeformed<'t>>, pub dsh: Option<StageDeformed<'t>>
}
#[derive(Debug)]
pub struct StageDeformed<'t>
{
    pub bindings: BoundMap<'t>, pub io: IOSemanticsMap<'t>, pub types: DeformedTypes<'t>
}
#[derive(Debug)]
pub struct ConstantDef<'t>
{
    pub type_hint: Option<deformer::FullTy<'t, 't>>, pub default_expr: Option<deformer::Expr<'t, 't>>
}
#[derive(Debug)]
pub enum BindingTree<'t>
{
    /// x...
    Expr(deformer::Expr<'t, 't>),
    /// \<pat>. x...
    WithArgument(deformer::ExprPat<'t, 't>, Box<BindingTree<'t>>)
}
#[derive(Debug)]
pub struct Binding<'t> { pub type_hint: Option<deformer::FullTy<'t, 't>>, pub tree: BindingTree<'t> }

#[derive(Debug, Clone, Copy, PartialEq, Eq)] pub enum RegisterResult { Success, Exists }

#[derive(Debug)]
pub struct IOSemanticsMap<'t>
{
    pub inputs: HashMap<Semantics, (&'t str, BType)>,
    pub outputs: HashMap<Semantics, (Option<&'t str>, Option<BType>, deformer::Expr<'t, 't>)>
}
#[derive(Debug)]
pub struct BoundMap<'t>
{
    pub uniforms: HashMap<&'t str, deformer::FullTy<'t, 't>>,
    pub constants: HashMap<&'t str, ConstantDef<'t>>,
    pub defs: HashMap<Cow<'t, str>, Vec<Binding<'t>>>,
}
#[derive(Debug)]
pub struct DeformedTypes<'t>
{
    pub fns: HashMap<&'t str, (deformer::Ty<'t, 't>, Option<deformer::FullTy<'t, 't>>)>,
    pub data: HashMap<&'t str, HashMap<&'t str, deformer::Ty<'t, 't>>>
}
impl<'t> IOSemanticsMap<'t>
{
    fn new() -> Self { IOSemanticsMap { inputs: HashMap::new(), outputs: HashMap::new() } }
    fn register_input(&mut self, sem: Semantics, name: &'t str, type_: BType) -> RegisterResult
    {
        if self.inputs.contains_key(&sem) { RegisterResult::Exists }
        else { self.inputs.insert(sem, (name, type_)); RegisterResult::Success }
    }
    fn register_output(&mut self, sem: Semantics, name: Option<&'t str>, type_hint: Option<BType>, expr: deformer::Expr<'t, 't>) -> RegisterResult
    {
        if self.outputs.contains_key(&sem) { RegisterResult::Exists }
        else { self.outputs.insert(sem, (name, type_hint, expr)); RegisterResult::Success }
    }
}
impl<'t> BoundMap<'t>
{
    fn new() -> Self { BoundMap { uniforms: HashMap::new(), constants: HashMap::new(), defs: HashMap::new() } }
    fn register_uniform(&mut self, name: &'t str, type_: deformer::FullTy<'t, 't>) -> RegisterResult
    {
        if self.uniforms.contains_key(name) { RegisterResult::Exists }
        else { self.uniforms.insert(name, type_); RegisterResult::Success }
    }
    fn register_constant(&mut self, name: &'t str, details: ConstantDef<'t>) -> RegisterResult
    {
        if self.constants.contains_key(name) { RegisterResult::Exists }
        else { self.constants.insert(name, details); RegisterResult::Success }
    }
    fn register<N: Into<Cow<'t, str>>>(&mut self, name: N, tree: Binding<'t>)
    {
        self.defs.entry(name.into()).or_insert_with(Vec::new).push(tree);
    }
}
impl<'t> DeformedTypes<'t>
{
    fn new() -> Self { DeformedTypes { fns: HashMap::new(), data: HashMap::new() } }
    fn register_fn(&mut self, name: &'t str, left: deformer::Ty<'t, 't>, right: deformer::FullTy<'t, 't>) -> RegisterResult
    {
        if self.fns.contains_key(name) { RegisterResult::Exists }
        else { self.fns.insert(name, (left, Some(right))); RegisterResult::Success }
    }
    fn register(&mut self, name: &'t str, left: deformer::Ty<'t, 't>) -> RegisterResult
    {
        if self.fns.contains_key(name) { RegisterResult::Exists }
        else { self.fns.insert(name, (left, None)); RegisterResult::Success }
    }
    fn register_data_ctor(&mut self, tyname: &'t str, ctor_name: &'t str, ctor: deformer::Ty<'t, 't>) -> RegisterResult
    {
        let ref mut dscope = self.data.entry(tyname).or_insert(HashMap::new());
        if dscope.contains_key(ctor_name) { RegisterResult::Exists }
        else { dscope.insert(ctor_name, ctor); RegisterResult::Success }
    }
}

fn nth_tuple<'s: 't, 't>(index: deformer::Expr<'s, 't>, target: deformer::Expr<'s, 't>) -> deformer::Expr<'s, 't>
{
    static FUNC_IDENT: Source<'static> = Source { slice: "nth_tuple", pos: Location::EMPTY };
    deformer::Expr::Apply(box deformer::Expr::SymReference(GenSource::from(&FUNC_IDENT)), vec![index, target])
}

impl<'s> parser::ShaderStageDefinition<'s>
{
    pub fn deform<'t>(&'t self) -> Result<StageDeformed<'t>, Vec<ComplexDeformationError<'t>>> where 's: 't
    {
        let mut errors = Vec::new();
        let (mut io, mut bindings) = (IOSemanticsMap::new(), BoundMap::new());
        let assoc = self.assoc_env().borrow();
        
        for (name, si) in self.inputs.iter().filter_map(|si| si.name.map(|n| (n, si)))
        {
            if io.register_input(si.semantics, name, si._type) == RegisterResult::Exists
            {
                errors.place_back() <- ComplexDeformationError::SemanticsConflict(si.semantics, si.location.clone());
            }
        }
        for so in &self.outputs
        {
            let expr = CollectErrors!(so.expr.deform(&assoc) =>? errors; continue);
            if io.register_output(so.semantics, so.name, so._type.clone(), expr) == RegisterResult::Exists
            {
                errors.place_back() <- ComplexDeformationError::SemanticsConflict(so.semantics, so.location.clone());
            }
        }
        for (name, c) in self.constants.iter().filter_map(|c| c.name.map(|n| (n, c)))
        {
            let type_hint = CollectErrors!(opt c._type.as_ref().map(|x| x.deform(&assoc)) =>? errors; continue);
            let default_expr = CollectErrors!(opt c.value.as_ref().map(|x| x.deform(&assoc)) =>? errors; continue);
            if bindings.register_constant(name, ConstantDef { type_hint, default_expr }) == RegisterResult::Exists
            {
                errors.place_back() <- ComplexDeformationError::SymbolConflict(SymbolDomain::ConstantName, name, c.location.clone());
            }
        }
        for (name, u) in self.uniforms.iter().filter_map(|u| u.name.map(|n| (n, u)))
        {
            let type_ = CollectErrors!(u._type.deform(&assoc) =>? errors; continue);
            if bindings.register_uniform(name, type_) == RegisterResult::Exists
            {
                errors.place_back() <- ComplexDeformationError::SymbolConflict(SymbolDomain::UniformName, name, u.location.clone());
            }
        }
        for v in &self.values { errors.append(&mut parse_binding(v, &assoc, &mut bindings)); }
        let types = match parse_types(self, &assoc) { Ok(v) => v, Err(mut es) => { errors.append(&mut es); return Err(errors); } };

        if errors.is_empty() { Ok(StageDeformed { bindings, io, types }) } else { Err(errors) }
    }
}
impl<'s> parser::ShadingPipeline<'s>
{
    pub fn deform<'t>(&'t self) -> Result<PipelineDeformed<'t>, Vec<ComplexDeformationError<'t>>> where 's: 't
    {
        let mut errors = Vec::new();
        let mut bindings = BoundMap::new();
        let assoc = self.assoc.borrow();

        let vsh = ::reverse_opt_res(self.vsh.as_ref().map(|x| x.deform()))?;
        let hsh = ::reverse_opt_res(self.hsh.as_ref().map(|x| x.deform()))?;
        let dsh = ::reverse_opt_res(self.dsh.as_ref().map(|x| x.deform()))?;
        let gsh = ::reverse_opt_res(self.gsh.as_ref().map(|x| x.deform()))?;
        let fsh = ::reverse_opt_res(self.fsh.as_ref().map(|x| x.deform()))?;
        for v in &self.values { errors.append(&mut parse_binding(v, &assoc, &mut bindings)); }
        let types = match parse_types(self, &assoc) { Ok(v) => v, Err(mut es) => { errors.append(&mut es); return Err(errors); } };

        if errors.is_empty() { Ok(PipelineDeformed { bindings, vsh, hsh, dsh, gsh, fsh, types }) } else { Err(errors) }
    }
}

enum OptionalSpan<'s: 't, 't> { None(&'t Location), Some(GenSource<'s, 't>) }
impl<'s: 't, 't> OptionalSpan<'s, 't>
{
    fn text(&self) -> &str { match *self { OptionalSpan::None(_) => "_", OptionalSpan::Some(ref s) => s.text() } }
}
fn parse_binding<'s: 't, 't>(v: &'t parser::ValueDeclaration<'s>, assoc: &AssociativityEnv<'s>, bindings: &mut BoundMap<'t>) -> Vec<ComplexDeformationError<'t>>
{
    let mut errors = Vec::new();
    let (lhs, rhs_opt, type_hint) = (v.pattern().deform(assoc), ::reverse_opt_res(v.value().map(|x| x.deform(assoc))), ::reverse_opt_res(v.type_hint().map(|x| x.deform(assoc))));
    if let Err(ref e) = lhs { errors.place_back() <- e.clone().into(); }
    if let Err(ref e) = rhs_opt { errors.place_back() <- e.clone().into(); }
    if let Err(ref e) = type_hint { errors.place_back() <- e.clone().into(); }
    if !errors.is_empty() { return errors; }
    let (lhs, rhs, type_hint) = (lhs.unwrap(), rhs_opt.unwrap(), type_hint.unwrap());
    if rhs.is_none() { return errors; }
    let rhs = rhs.unwrap();

    fn boundable<'s: 't, 't, 'd>(t: &'d deformer::ExprPat<'s, 't>) -> Result<OptionalSpan<'s, 't>, &'d Location>
    {
        match *t
        {
            deformer::ExprPat::SymBinding(ref s) => Ok(OptionalSpan::Some(s.clone())),
            deformer::ExprPat::Placeholder(p) => Ok(OptionalSpan::None(p)),
            _ => Err(t.position())
        }
    }
    match lhs
    {
        // tuple pattern: (a, b) = f x => #tup_(a,b) = f x; a = nth_tuple 0 #tup_(a,b); b = nth_tuple 1 #tup_(a,b)
        deformer::ExprPat::Tuple(t0, ts) =>
        {
            let (b0, bs) = (boundable(&t0), ts.iter().map(boundable).collect::<Result<Vec<_>, _>>());
            if let Err(p) = b0 { errors.place_back() <- ComplexDeformationError::Unboundable(p.clone()); }
            if let Err(p) = bs { errors.place_back() <- ComplexDeformationError::Unboundable(p.clone()); }
            if !errors.is_empty() { return errors; }
            let (b0, bs) = (b0.unwrap(), bs.unwrap());

            let decons_name = format!("#tup_({},{})", b0.text(), bs.iter().map(OptionalSpan::text).collect::<Vec<_>>().join(","));
            bindings.register(decons_name.clone(), Binding { type_hint, tree: BindingTree::Expr(rhs) });
            let decons_t = deformer::Expr::SymReference(GenSource::Generated(decons_name));
            if let OptionalSpan::Some(b0) = b0
            {
                let index = deformer::Expr::Numeric(GenNumeric::from(0));
                bindings.register(b0.text().to_owned(), Binding { type_hint: None, tree: BindingTree::Expr(nth_tuple(index, decons_t.clone())) });
            }
            for (i, n) in bs.into_iter().enumerate()
            {
                if let OptionalSpan::Some(n) = n
                {
                    let index = deformer::Expr::Numeric(GenNumeric::from(i as u64 + 1));
                    bindings.register(n.text().to_owned(), Binding { type_hint: None, tree: BindingTree::Expr(nth_tuple(index, decons_t.clone())) });
                }
            }
        },
        // simple applying pattern: a n = n + 2 => a = \n. n + 2
        deformer::ExprPat::Apply(SymPath { base, desc }, args) => if desc.is_empty()
        {
            let rhs = args.into_iter().rev().fold(BindingTree::Expr(rhs), |r, a| BindingTree::WithArgument(a, box r));
            bindings.register(base.text().to_owned(), Binding { type_hint, tree: rhs });
        }
        else { errors.place_back() <- ComplexDeformationError::Unboundable(base.position().clone()); },
        // simple binding pattern: a = 2
        deformer::ExprPat::SymBinding(name) => { bindings.register(name.text().to_owned(), Binding { type_hint, tree: BindingTree::Expr(rhs) }); },
        _ => { errors.place_back() <- ComplexDeformationError::Unboundable(lhs.position().clone()); }
    }
    errors
}
fn parse_types<'s: 't, 't, Tree: parser::TypeDeclarable<'s> + 't>(tree: &'t Tree, assoc: &AssociativityEnv<'s>) -> Result<DeformedTypes<'t>, Vec<ComplexDeformationError<'t>>>
{
    let (mut set, mut errors) = (DeformedTypes::new(), Vec::new());

    for t in tree.type_fns()
    {
        for &(ref left, ref right) in &t.defs
        {
            let left_d = CollectErrors!(left.deform(assoc) =>? errors; continue);
            let right = CollectErrors!(right.deform(assoc) =>? errors; continue);
            let name = if let deformer::Ty::Expressed(deformer::Prefix::User(ref s), _) = left_d { s.slice }
            else { errors.place_back() <- ComplexDeformationError::Unboundable(left.position().clone()); continue; };
            if set.register_fn(name, left_d, right) == RegisterResult::Exists
            {
                errors.place_back() <- ComplexDeformationError::SymbolConflict(SymbolDomain::TypeSynonymName, name, left.position().clone());
            }
        }
    }
    for d in tree.type_decls()
    {
        for &(ref dt, ref ds) in &d.defs
        {
            let ty = CollectErrors!(dt.deform(assoc) =>? errors; continue);
            let tyname = match ty.leftmost_symbol()
            {
                Some(&deformer::Prefix::User(s)) => s.slice,
                _ => { errors.place_back() <- ComplexDeformationError::Undefineable(ty.position().clone()); continue; }
            };
            if set.register(tyname, ty) == RegisterResult::Exists
            {
                errors.place_back() <- ComplexDeformationError::SymbolConflict(SymbolDomain::TypeName, tyname, dt.position().clone());
            }

            for c in ds
            {
                let ctor = CollectErrors!(c.tree.deform(assoc) =>? errors; continue);
                let ctor_name = match ctor
                {
                    deformer::Ty::Expressed(deformer::Prefix::User(name), _) => name.slice,
                    _ => { errors.place_back() <- ComplexDeformationError::Undefineable(ctor.position().clone()); continue; }
                };
                if set.register_data_ctor(tyname, ctor_name, ctor) == RegisterResult::Exists
                {
                    errors.place_back() <- ComplexDeformationError::SymbolConflict(SymbolDomain::DataConstructorName, ctor_name, c.tree.position().clone());
                }
            }
        }
    }

    if errors.is_empty() { Ok(set) } else { Err(errors) }
}

#[derive(Debug)]
pub enum ComplexDeformationError<'s>
{
    Inherit(DeformationError), SemanticsConflict(Semantics, Location), SymbolConflict(SymbolDomain, &'s str, Location), Unboundable(Location),
    Undefineable(Location)
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolDomain { ConstantName, UniformName, TypeSynonymName, TypeName, DataConstructorName }
impl<'s> From<DeformationError> for ComplexDeformationError<'s> { fn from(v: DeformationError) -> Self { ComplexDeformationError::Inherit(v) } }

use {PrettyPrintSink, PrettyPrint}; use std::io::{Write, Result as IOResult};
impl<'t> PrettyPrint for PipelineDeformed<'t>
{
    fn pretty_print<W: Write>(&self, sink: &mut W) -> IOResult<()>
    {
        sink.print(b"Bindings: \n")?.pretty_sink(&self.bindings)?;
        sink.print(b"Types: \n")?.pretty_sink(&self.types)?;
        if let Some(ref v) = self.vsh { sink.print(b"in Vertex Stage: \n")?.pretty_sink(v)?; }
        if let Some(ref v) = self.hsh { sink.print(b"in Hull Stage: \n")?.pretty_sink(v)?; }
        if let Some(ref v) = self.dsh { sink.print(b"in Domain Stage: \n")?.pretty_sink(v)?; }
        if let Some(ref v) = self.gsh { sink.print(b"in Geometry Stage: \n")?.pretty_sink(v)?; }
        if let Some(ref v) = self.fsh { sink.print(b"in Fragment Stage: \n")?.pretty_sink(v)?; }
        Ok(())
    }
}
impl<'t> PrettyPrint for StageDeformed<'t>
{
    fn pretty_print<W: Write>(&self, sink: &mut W) -> IOResult<()>
    {
        sink.print(b"IO Semantics: \n")?.pretty_sink(&self.io)?;
        sink.print(b"Bindings: \n")?.pretty_sink(&self.bindings)?;
        sink.print(b"Types: \n")?.pretty_sink(&self.types).map(drop)
    }
}
impl<'t> PrettyPrint for BoundMap<'t>
{
    fn pretty_print<W: Write>(&self, sink: &mut W) -> IOResult<()>
    {
        for (&name, c) in &self.constants
        {
            write!(sink, "- [constant] {}: ", name)?;
            if let Some(ref th) = c.type_hint { th.pretty_print(sink)?; } else { write!(sink, "_")?; }
            if let Some(ref x) = c.default_expr { sink.print(b" = ")?.pretty_sink(x)?; }
            write!(sink, "\n")?;
        }
        for (&name, th) in &self.uniforms
        {
            write!(sink, "- [uniform] {}: ", name)?;
            th.pretty_print(sink)?; write!(sink, "\n")?;
        }
        for (name, b) in &self.defs
        {
            for b1 in b
            {
                write!(sink, "- {}: ", name)?;
                if let Some(ref th) = b1.type_hint { th.pretty_print(sink)?; } else { write!(sink, "_")?; }
                sink.print(b" = ")?.pretty_sink(&b1.tree)?.print(b"\n")?;
            }
        }
        Ok(())
    }
}
impl<'t> PrettyPrint for IOSemanticsMap<'t>
{
    fn pretty_print<W: Write>(&self, sink: &mut W) -> IOResult<()>
    {
        for (&sem, &(name, ty)) in &self.inputs { write!(sink, "- [input:{}] {}: {}\n", sem, name, ty)?; }
        for (&sem, &(name, ref th, ref expr)) in &self.outputs
        {
            write!(sink, "- [output:{}] {}: ", sem, name.map_or("_".to_owned(), ToString::to_string))?;
            if let &Some(ref th) = th { write!(sink, "{}", th)?; } else { write!(sink, "_")?; }
            sink.print(b" = ")?.pretty_sink(expr)?.print(b"\n")?;
        }
        Ok(())
    }
}
impl<'t> PrettyPrint for DeformedTypes<'t>
{
    fn pretty_print<W: Write>(&self, sink: &mut W) -> IOResult<()>
    {
        for (name, &(ref lty, ref rty)) in &self.fns
        {
            if let &Some(ref rty) = rty
            {
                write!(sink, "- [type synonym] {}(", name)?; sink.pretty_sink(lty)?.print(b") = ")?.pretty_sink(rty)?;
            }
            else { write!(sink, "- [data type] {}(", name)?; sink.pretty_sink(lty)?.print(b")")?; }
            write!(sink, "\n")?;
        }
        for (tyname, ctors) in &self.data
        {
            for (ctor_name, ctor_form) in ctors
            {
                write!(sink, "- [data constructor for {}] {} = ", tyname, ctor_name)?;
                sink.pretty_sink(ctor_form)?.print(b"\n")?;
            }
        }
        Ok(())
    }
}
impl<'t> PrettyPrint for BindingTree<'t>
{
    fn pretty_print<W: Write>(&self, sink: &mut W) -> IOResult<()>
    {
        match *self
        {
            BindingTree::Expr(ref x) => x.pretty_print(sink),
            BindingTree::WithArgument(ref p, ref c) => sink.pretty_sink(p)?.print(b" [~>] ")?.pretty_sink(c).map(drop)
        }
    }
}
