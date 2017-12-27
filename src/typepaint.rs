//! Type Painter

use std::collections::{HashMap, HashSet};
use std::rc::{Rc, Weak};
use super::parser::*;
use super::{Source, Location, BType};
use std::mem::replace;

pub trait AssociativityDebugPrinter
{
    fn dbg_print_assoc(&self, indent: usize);
}
impl<'s> AssociativityDebugPrinter for ::ShadingPipeline<'s>
{
    fn dbg_print_assoc(&self, indent: usize)
    {
        println!("{}Assoc in ShadingPipeline: {:?}", " ".repeat(indent), self.assoc.borrow().ops);
        if let Some(ref p) = self.vsh { p.dbg_print_assoc(indent + 1); }
        if let Some(ref p) = self.hsh { p.dbg_print_assoc(indent + 1); }
        if let Some(ref p) = self.dsh { p.dbg_print_assoc(indent + 1); }
        if let Some(ref p) = self.gsh { p.dbg_print_assoc(indent + 1); }
        if let Some(ref p) = self.fsh { p.dbg_print_assoc(indent + 1); }
    }
}
impl<'s> AssociativityDebugPrinter for ::ShaderStageDefinition<'s>
{
    fn dbg_print_assoc(&self, indent: usize)
    {
        println!("{}Assoc in ShaderStageDef: {:?}", " ".repeat(indent), self.assoc.borrow().ops);
    }
}

use std::cell::RefCell;
pub type RcMut<T> = Rc<RefCell<T>>; pub type WeakMut<T> = Weak<RefCell<T>>;
pub fn new_rcmut<T>(init: T) -> RcMut<T> { Rc::new(RefCell::new(init)) }

pub struct ConstructorEnv<'s>
{
    pub ty: HashSet<&'s str>, pub data: HashMap<&'s str, Vec<&'s str>>
}
impl<'s> ConstructorEnv<'s>
{
    fn new() -> Self { ConstructorEnv { ty: HashSet::new(), data: HashMap::new() } }
    fn is_empty(&self) -> bool { self.ty.is_empty() && self.data.is_empty() }
}
pub trait ConstructorCollector<'s>
{
    type Env: 's;
    fn collect_ctors(&self, env: &RcMut<Self::Env>);
}
pub trait ConstructorEnvironment<'s>
{
    fn symbol_set(&self) -> &ConstructorEnv<'s>;
    fn drop_if_empty(this: RcMut<Self>) -> Option<RcMut<Self>>
    {
        if this.borrow().symbol_set().is_empty() { None } else { Some(this) }
    }
}

pub struct ShadingPipelineConstructorEnv<'s>
{
    vsh: Option<RcMut<ConstructorEnvPerShader<'s>>>, hsh: Option<RcMut<ConstructorEnvPerShader<'s>>>, dsh: Option<RcMut<ConstructorEnvPerShader<'s>>>,
    gsh: Option<RcMut<ConstructorEnvPerShader<'s>>>, fsh: Option<RcMut<ConstructorEnvPerShader<'s>>>, pub set: ConstructorEnv<'s>
}
impl<'s> ConstructorEnvironment<'s> for ShadingPipelineConstructorEnv<'s> { fn symbol_set(&self) -> &ConstructorEnv<'s> { &self.set } }
impl<'s> ShadingPipelineConstructorEnv<'s>
{
    pub fn new() -> RcMut<Self>
    {
        new_rcmut(ShadingPipelineConstructorEnv { vsh: None, hsh: None, dsh: None, gsh: None, fsh: None, set: ConstructorEnv::new() })
    }
}
impl<'s> ConstructorCollector<'s> for ::ShadingPipeline<'s>
{
    type Env = ShadingPipelineConstructorEnv<'s>;
    fn collect_ctors(&self, env: &RcMut<Self::Env>)
    {
        if let Some(ref v) = self.vsh { env.borrow_mut().vsh = collect_ctors_in_shader(env, v); }
        if let Some(ref v) = self.hsh { env.borrow_mut().hsh = collect_ctors_in_shader(env, v); }
        if let Some(ref v) = self.dsh { env.borrow_mut().dsh = collect_ctors_in_shader(env, v); }
        if let Some(ref v) = self.gsh { env.borrow_mut().gsh = collect_ctors_in_shader(env, v); }
        if let Some(ref v) = self.fsh { env.borrow_mut().fsh = collect_ctors_in_shader(env, v); }
        collect_for_type_decls(env, self);
    }
}
pub struct ConstructorEnvPerShader<'s> { parent: WeakMut<ShadingPipelineConstructorEnv<'s>>, pub set: ConstructorEnv<'s> }
impl<'s> ConstructorEnvironment<'s> for ConstructorEnvPerShader<'s> { fn symbol_set(&self) -> &ConstructorEnv<'s> { &self.set } }
impl<'s> ConstructorCollector<'s> for ::ShaderStageDefinition<'s>
{
    type Env = ConstructorEnvPerShader<'s>;
    fn collect_ctors(&self, env: &RcMut<Self::Env>) { collect_for_type_decls(env, self); }
}
fn collect_ctors_in_shader<'s>(parent: &RcMut<ShadingPipelineConstructorEnv<'s>>, sh: &::ShaderStageDefinition<'s>) -> Option<RcMut<ConstructorEnvPerShader<'s>>>
{
    let e = new_rcmut(ConstructorEnvPerShader { parent: Rc::downgrade(parent), set: ConstructorEnv::new() });
    sh.collect_ctors(&e); ConstructorEnvironment::drop_if_empty(e)
}
fn collect_for_type_decls<'s, Env: ConstructorEnvironment<'s>, T: ::TypeDeclarable<'s>>(env: &RcMut<Env>, tree: &T)
{
    for &(ref ty, ref defs) in tree.type_decls().iter().flat_map(|td| &td.defs)
    {
        println!("**dbg** Found Type Constructor: {:?}", ty);
        let dcons: Vec<_> = defs.iter().map(|dc| dc.name).collect();
        println!("**dbg** Found Data Constructor for {:?} = {:?}", ty, dcons);
    }
    for &(ref tys, _) in tree.type_fns().iter().flat_map(|tf| &tf.defs)
    {
        println!("**dbg** Found Type Constructor: {:?}", tys);
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Prefix<'s: 't, 't> { Arrow, User(&'t Source<'s>), PathRef(Box<TyDeformerIntermediate<'s, 't>>, Vec<&'t Source<'s>>) }
impl<'s: 't, 't> Prefix<'s, 't>
{
    pub fn is_equal_nolocation(&self, other: &Self) -> bool
    {
        match *self
        {
            Prefix::Arrow => *other == Prefix::Arrow,
            Prefix::User(&Source { slice, .. }) => if let Prefix::User(&Source { slice: slice_, .. }) = *other { slice == slice_ } else { false },
            Prefix::PathRef(ref p, ref v) => if let Prefix::PathRef(ref p_, ref v_) = *other
            {
                p.is_equal_nolocation(&p_) && v.len() == v_.len() && v.iter().zip(v_.iter()).all(|(a, b)| a.slice == b.slice)
            }
            else { false }
        }
    }
}
#[derive(Debug, PartialEq, Eq)]
pub enum TyDeformerIntermediate<'s: 't, 't>
{
    Placeholder(&'t Location), Expressed(Prefix<'s, 't>, Vec<TyDeformerIntermediate<'s, 't>>),
    SafetyGarbage, Basic(&'t Location, BType), Tuple(&'t Location, Vec<TyDeformerIntermediate<'s, 't>>),
    ArrayDim(Box<TyDeformerIntermediate<'s, 't>>, &'t InferredArrayDim<'s>)
}
pub struct InfixIntermediate<'s: 't, 't, IR: 't> { op: &'t Source<'s>, assoc: Associativity, ir: IR }
impl<'s: 't, 't> TyDeformerIntermediate<'s, 't>
{
    /// self <+> (new_lhs new_arg) = (new_lhs self new_arg)
    fn combine(self, new_lhs: Prefix<'s, 't>, new_arg: Self) -> Self
    {
        TyDeformerIntermediate::Expressed(new_lhs, vec![self, new_arg])
    }
    fn combine_inplace(&mut self, new_lhs: Prefix<'s, 't>, new_arg: Self) -> &mut Self
    {
        let old = replace(self, TyDeformerIntermediate::SafetyGarbage);
        *self = old.combine(new_lhs, new_arg); self
    }
    fn append_args(&mut self, new_args: &mut Vec<Self>)
    {
        match *self
        {
            TyDeformerIntermediate::Expressed(_, ref mut args) => args.append(new_args),
            _ => unreachable!()
        }
    }

    pub fn is_equal_nolocation(&self, other: &Self) -> bool
    {
        match *self
        {
            TyDeformerIntermediate::Placeholder(_) => if let TyDeformerIntermediate::Placeholder(_) = *other { true } else { false },
            TyDeformerIntermediate::Expressed(ref p, ref v) => if let TyDeformerIntermediate::Expressed(ref p_, ref v_) = *other
            {
                p.is_equal_nolocation(&p_) && v.len() == v_.len() && v.iter().zip(v_.iter()).all(|(s, o)| s.is_equal_nolocation(o))
            }
            else { false },
            TyDeformerIntermediate::SafetyGarbage => unreachable!(),
            TyDeformerIntermediate::Basic(_, bt) => if let TyDeformerIntermediate::Basic(_, bt_) = *other { bt == bt_ } else { false },
            TyDeformerIntermediate::Tuple(_, ref v) => if let TyDeformerIntermediate::Tuple(_, ref v_) = *other
            {
                v.len() == v_.len() && v.iter().zip(v_.iter()).all(|(s, o)| s.is_equal_nolocation(o))
            }
            else { false },
            TyDeformerIntermediate::ArrayDim(ref p, ref e) => if let TyDeformerIntermediate::ArrayDim(ref p_, ref e_) = *other
            {
                p.is_equal_nolocation(&p_) && e == e_
            }
            else { false }
        }
    }
}

#[derive(Debug)] pub enum DeformationError<'t>
{
    ArgumentRequired(&'t Location), UnresolvedAssociation(&'t Location), ConstructorRequired(&'t Location),
    ApplicationProhibited(&'t Location)
}
pub fn deform_ty<'s: 't, 't>(ty: &'t TypeSynTree<'s>, assoc_env: &AssociativityEnv<'s>) -> Result<TyDeformerIntermediate<'s, 't>, DeformationError<'t>>
{
    match *ty
    {
        // a b... => (deform(a), sym_placeholder(b...))
        TypeSynTree::Prefix(ref v) =>
        {
            let mut lhs = deform_ty(v.first().expect("Empty PrefixTy"), assoc_env)?;
            let mut add_args = v[1..].iter().map(|t| deform_ty(t, assoc_env)).collect::<Result<_, _>>()?;
            lhs.append_args(&mut add_args);
            Ok(lhs)
        },
        TypeSynTree::Infix { ref lhs, ref mods } =>
        {
            let mut mods: Vec<_> = mods.iter().map(|&(ref op, ref rhs)| Ok(InfixIntermediate
            {
                op, assoc: assoc_env.lookup(op.slice), ir: deform_ty(rhs, assoc_env)?
            })).collect::<Result<_, _>>()?;
            let mut lhs = deform_ty(lhs, assoc_env)?;
            while !mods.is_empty()
            {
                let agg = extract_most_precedences(&mods).map_err(DeformationError::UnresolvedAssociation)?.unwrap();
                let ir = mods.remove(agg.index);
                let cell = if agg.index >= 1 { &mut mods[agg.index - 1].ir } else { &mut lhs };
                cell.combine_inplace(Prefix::User(&ir.op), ir.ir);
            }
            Ok(lhs)
        },
        // a => a, []
        TypeSynTree::SymReference(ref sym) => Ok(TyDeformerIntermediate::Expressed(Prefix::User(sym), Vec::new())),
        TypeSynTree::PathRef(ref base, ref v) => Ok(TyDeformerIntermediate::Expressed(Prefix::PathRef(box deform_ty(base, assoc_env)?, v.iter().collect()), Vec::new())),
        TypeSynTree::Placeholder(ref p) => Ok(TyDeformerIntermediate::Placeholder(p)),
        TypeSynTree::Basic(ref p, bt) => Ok(TyDeformerIntermediate::Basic(p, bt)),
        TypeSynTree::Tuple(ref p, ref v) => Ok(TyDeformerIntermediate::Tuple(p, v.iter().map(|t| deform_ty(t, assoc_env)).collect::<Result<_, _>>()?)),
        TypeSynTree::ArrowInfix { ref lhs, ref rhs } => Ok(TyDeformerIntermediate::Expressed(Prefix::Arrow, vec![deform_ty(lhs, assoc_env)?, deform_ty(rhs, assoc_env)?])),
        TypeSynTree::ArrayDim { ref lhs, ref num } => Ok(TyDeformerIntermediate::ArrayDim(box deform_ty(lhs, assoc_env)?, num))
    }
}

fn ap_2options<A, F: FnOnce(A, A) -> bool>(cond: F, t: Option<A>, f: Option<A>) -> Option<bool>
{
    if t.is_none() && f.is_none() { None } else { Some(t.map_or(false, |t| f.map_or(true, |f| cond(t, f)))) }
}

#[derive(Clone)]
pub struct AggPointer { prec: usize, index: usize }
fn extract_most_precedences1<'s: 't, 't, IR: 's>(mods: &[InfixIntermediate<'s, 't, IR>])
    -> Result<(Option<AggPointer>, Option<AggPointer>, Option<AggPointer>), &'t Location>
{
    let (mut left, mut right, mut none): (Option<AggPointer>, Option<AggPointer>, Option<AggPointer>) = (None, None, None);
    let mut none_last_prec = None;
    for (i, ir) in mods.iter().enumerate()
    {
        match ir.assoc
        {
            Associativity::Left(prec) =>
            {
                if left.as_ref().map_or(true, |t| prec > t.prec) { left = Some(AggPointer { prec, index: i }); }
                none_last_prec = None;
            },
            Associativity::Right(prec) =>
            {
                if right.as_ref().map_or(true, |t| prec >= t.prec) { right = Some(AggPointer { prec, index: i }); }
                none_last_prec = None;
            },
            Associativity::None(prec) if none_last_prec == Some(prec) => return Err(&ir.op.pos),
            Associativity::None(prec) =>
            {
                if none.as_ref().map_or(true, |t| prec > t.prec) { none = Some(AggPointer { prec, index: i }); }
                none_last_prec = Some(prec);
            }
        }
    }
    Ok((left, right, none))
}
pub fn extract_most_precedences<'s: 't, 't, IR: 's>(mods: &[InfixIntermediate<'s, 't, IR>]) -> Result<Option<AggPointer>, &'t Location>
{
    let (l, r, n) = extract_most_precedences1(mods)?;
    Ok(ap_2options(|l, r| l.prec > r.prec, l.as_ref(), r.as_ref()).map_or(n.clone(), |llarge| if llarge
    {
        ap_2options(|n, l| n.prec > l.prec, n.as_ref(), l.as_ref()).map(|nlarge| if nlarge { n.unwrap() } else { l.unwrap() })
    }
    else
    {
        ap_2options(|n, r| n.prec > r.prec, n.as_ref(), r.as_ref()).map(|nlarge| if nlarge { n.unwrap() } else { r.unwrap() })
    }))
}

/*
pub struct TyConstructorEnv<'s>
{
    /// Type constructor(A in `type A b`, D in `data D a = ...`)
    pub tycons: HashSet<&'s str>,
    /// Data constructors(map of (constructor_ident, generated_tycons_candidates))
    pub datacons: HashMap<&'s str, Vec<&'s str>>,
    /// Children scope
    pub children: Vec<TyConstructorEnv<'s>>
}
pub trait TyConstructorCollectable<'s>
{
    fn collect(&self, scope: &mut TyConstructorEnv<'s>);
}
impl<'s> TyConstructorCollectable<'s> for TypeDeclaration<'s>
{
    fn collect(&self, scope: &mut TyConstructorEnv<'s>)
    {
        for (tycons, datacons_list) in self.defs.iter()
        {
            scope.tycons.insert(tycons);
        }
    }
}
*/
/*
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyKind { Seed, Arrow(Box<TyKind>, Box<TyKind>), Prior(Box<TyKind>) }
pub type TySymbolKey<'s> = &'s str;
pub type TyOperatorKey<'s> = &'s str;
pub type SymbolKey<'s> = &'s str;
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopeTypeSymbolDefs<'s>
{
    pub types: HashMap<TySymbolKey<'s>, TyKind>,
    pub placeholders: HashSet<TySymbolKey<'s>>,
    pub ops: HashMap<TyOperatorKey<'s>, TyKind>,
    pub children: Vec<Rc<ScopeTypeSymbolDefs<'s>>>, pub parent: Option<Weak<ScopeTypeSymbolDefs<'s>>>
}
impl<'s> ScopeTypeSymbolDefs<'s>
{
    pub fn lookup(&self, key: TySymbolKey<'s>) -> Option<&TyKind>
    {
        self.types.get(key).or_else(|| self.parent.as_ref().and_then(|p| p.lookup(key)))
    }
    pub fn lookup_op(&self, key: TyOperatorKey<'s>) -> Option<&TyKind>
    {
        self.types.get(key).or_else(|| self.parent.as_ref().and_then(|p| p.lookup(key)))
    }
    /*pub fn find(key: TySymbolKey<'s>) -> Option<&TyKind>
    {
        self.types.get(key).or_else(|| self.children.find(|c| c.find(key)))
    }
    pub fn find_op(key: TyOperatorKey<'s>) -> Option<&TyKind>
    {
        self.ops.get(key).or_else(|| self.children.find(|c| c.find_op(key)))
    }*/
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PaintedType<'s>
{
    Defined(TySymbolKey<'s>), Placeholder, NamedPlaceholder(TySymbolKey<'s>), BinaryOp(TyOperatorKey<'s>), ListOp(Option<Box<PaintedType>>), Prior(PaintedTypeString<'s>)
}
impl<'s> PaintedType<'s>
{
    pub fn convert(src: &TypeFragment<'s>, tysym_scope_current: &mut ScopeTypeSymbolDefs<'s>) -> Option<Self>
    {
        match *src
        {
            TypeFragment::UserType(Source { slice, .. }) => if tysym_scope_current.lookup(slice).is_some()
            {
                Some(PaintedType::Defined(slice))
            }
            else { tysym_scope_current.placeholders.insert(slice); Some(PaintedType::NamedPlaceholder(slice)) },
            TypeFragment::OpArrow(_) => Some(PaintedType::BinaryOp("->")),
            TypeFragment::OpConstraint(_) => Some(PaintedType::BinaryOp("=>")),
            TypeFragment::Operator(Source { slice, .. }) => if tysym_scope_current.lookup_op(slice).is_some()
            {
                Some(PaintedType::BinaryOp(slice))
            }
            else { None },
            TypeFragment::ArrayDim(_, ref inner) => inner.as_ref().map(|x| )
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PaintedTypeString<'s>(Vec<PaintedType<'s>>);*/

#[cfg(test)] mod tests
{
    use ::*;
    #[test] fn ty_unification()
    {
        fn test_unify<'s>(infix: &'s str, prefix: &'s str)
        {
            let case = TokenizerState::from(infix).strip_all();
            let case2 = TokenizerState::from(prefix).strip_all();
            let c1 = TypeSynTree::parse(&mut PreanalyzedTokenStream::from(&case[..]), Leftmost::Nothing).expect(&format!("in case infix({})", infix));
            let c2 = TypeSynTree::parse(&mut PreanalyzedTokenStream::from(&case2[..]), Leftmost::Nothing).expect(&format!("in case prefix({})", prefix));
            let assoc_env = AssociativityEnv::new(None);
            let c1d = deform_ty(&c1, &assoc_env).expect("in deforming case infix");
            let c2d = deform_ty(&c2, &assoc_env).expect("in deforming case prefix");
            assert!(c1d.is_equal_nolocation(&c2d), "not matching: {:?} and {:?}", c1d, c2d);
        }
        test_unify("a `Cons` b", "Cons a b");
        test_unify("(c + b) d", "(+) c b d");
        test_unify("c + d + e", "(+) ((+) c d) e");
    }
}
