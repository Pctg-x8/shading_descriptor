//! Type Painter

use std::collections::{HashMap, HashSet};
use std::rc::{Rc, Weak};
use super::parser::*;
use super::{Source, Location, BType};
use std::mem::replace;
use std::ops::DerefMut;

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

pub struct ConstructorEnv<'s: 't, 't>
{
    pub ty: HashSet<&'t Source<'s>>, pub data: HashMap<&'t Source<'s>, Vec<&'t Source<'s>>>
}
impl<'s: 't, 't> ConstructorEnv<'s, 't>
{
    fn new() -> Self { ConstructorEnv { ty: HashSet::new(), data: HashMap::new() } }
    fn is_empty(&self) -> bool { self.ty.is_empty() && self.data.is_empty() }
}
pub trait ConstructorCollector<'s: 't, 't>
{
    type Env: 't;
    fn collect_ctors(&'t self, env: &RcMut<Self::Env>) -> Result<(), Vec<ConstructorCollectionError<'t>>>;
}
pub trait ConstructorEnvironment<'s: 't, 't>
{
    fn symbol_set(&self) -> &ConstructorEnv<'s, 't>;
    fn symbol_set_mut(&mut self) -> &mut ConstructorEnv<'s, 't>;
    fn drop_if_empty(this: RcMut<Self>) -> Option<RcMut<Self>>
    {
        if this.borrow().symbol_set().is_empty() { None } else { Some(this) }
    }
}
#[derive(Debug)]
pub enum ConstructorCollectionError<'t>
{
    DeformingError(DeformationError<'t>), ConstructorNotFound(&'t Location), ArrowNotAllowed(&'t Location), PathRefNotAllowed(&'t Location)
}

// specialized constructor envs //
pub struct ShadingPipelineConstructorEnv<'s: 't, 't>
{
    pub vsh: Option<RcMut<ConstructorEnvPerShader<'s, 't>>>, pub hsh: Option<RcMut<ConstructorEnvPerShader<'s, 't>>>, pub dsh: Option<RcMut<ConstructorEnvPerShader<'s, 't>>>,
    pub gsh: Option<RcMut<ConstructorEnvPerShader<'s, 't>>>, pub fsh: Option<RcMut<ConstructorEnvPerShader<'s, 't>>>, pub set: ConstructorEnv<'s, 't>
}
impl<'s: 't, 't> ConstructorEnvironment<'s, 't> for ShadingPipelineConstructorEnv<'s, 't>
{
    fn symbol_set(&self) -> &ConstructorEnv<'s, 't> { &self.set }
    fn symbol_set_mut(&mut self) -> &mut ConstructorEnv<'s, 't> { &mut self.set }
}
impl<'s: 't, 't> ShadingPipelineConstructorEnv<'s, 't>
{
    pub fn new() -> RcMut<Self>
    {
        new_rcmut(ShadingPipelineConstructorEnv { vsh: None, hsh: None, dsh: None, gsh: None, fsh: None, set: ConstructorEnv::new() })
    }
}
pub struct ConstructorEnvPerShader<'s: 't, 't> { parent: WeakMut<ShadingPipelineConstructorEnv<'s, 't>>, pub set: ConstructorEnv<'s, 't> }
impl<'s: 't, 't> ConstructorEnvironment<'s, 't> for ConstructorEnvPerShader<'s, 't>
{
    fn symbol_set(&self) -> &ConstructorEnv<'s, 't> { &self.set }
    fn symbol_set_mut(&mut self) -> &mut ConstructorEnv<'s, 't> { &mut self.set }
}

impl<'s: 't, 't> ConstructorCollector<'s, 't> for ShadingPipeline<'s>
{
    type Env = ShadingPipelineConstructorEnv<'s, 't>;
    fn collect_ctors(&'t self, env: &RcMut<Self::Env>) -> Result<(), Vec<ConstructorCollectionError<'t>>>
    {
        fn collect_ctors_in_shader<'s: 't, 't>(parent: &RcMut<ShadingPipelineConstructorEnv<'s, 't>>, sh: &'t ShaderStageDefinition<'s>)
            -> Result<Option<RcMut<ConstructorEnvPerShader<'s, 't>>>, Vec<ConstructorCollectionError<'t>>>
        {
            let e = new_rcmut(ConstructorEnvPerShader { parent: Rc::downgrade(parent), set: ConstructorEnv::new() });
            sh.collect_ctors(&e).map(|_| ConstructorEnvironment::drop_if_empty(e))
        }

        let mut errors = Vec::new();
        if let Some(ref v) = self.vsh
        {
            match collect_ctors_in_shader(env, v)
            {
                Ok(e) => { env.borrow_mut().vsh = e; }, Err(mut ev) => errors.append(&mut ev)
            }
        }
        if let Some(ref v) = self.hsh
        {
            match collect_ctors_in_shader(env, v)
            {
                Ok(e) => { env.borrow_mut().hsh = e; }, Err(mut ev) => errors.append(&mut ev)
            }
        }
        if let Some(ref v) = self.dsh
        {
            match collect_ctors_in_shader(env, v)
            {
                Ok(e) => { env.borrow_mut().dsh = e; }, Err(mut ev) => errors.append(&mut ev)
            }
        }
        if let Some(ref v) = self.gsh
        {
            match collect_ctors_in_shader(env, v)
            {
                Ok(e) => { env.borrow_mut().gsh = e; }, Err(mut ev) => errors.append(&mut ev)
            }
        }
        if let Some(ref v) = self.fsh
        {
            match collect_ctors_in_shader(env, v)
            {
                Ok(e) => { env.borrow_mut().fsh = e; }, Err(mut ev) => errors.append(&mut ev)
            }
        }
        if let Err(mut e) = collect_for_type_decls(env.borrow_mut().deref_mut(), self) { errors.append(&mut e); }
        if errors.is_empty() { Ok(()) } else { Err(errors) }
    }
}
impl<'s: 't, 't> ConstructorCollector<'s, 't> for ShaderStageDefinition<'s>
{
    type Env = ConstructorEnvPerShader<'s, 't>;
    fn collect_ctors(&'t self, env: &RcMut<Self::Env>) -> Result<(), Vec<ConstructorCollectionError>> { collect_for_type_decls(env.borrow_mut().deref_mut(), self) }
}
fn collect_for_type_decls<'s: 't, 't, Env: ConstructorEnvironment<'s, 't>, T: TypeDeclarable<'s> + AssociativityEnvironment<'s>>(env: &mut Env, tree: &'t T)
    -> Result<(), Vec<ConstructorCollectionError<'t>>>
{
    let aenv = tree.assoc_env().borrow();
    let mut errors = Vec::new();
    for &(ref ty, ref defs) in tree.type_decls().iter().flat_map(|td| &td.defs)
    {
        let dty = match deform_ty(ty, &aenv).map_err(ConstructorCollectionError::DeformingError)
        {
            Ok(t) => t, Err(e) => { errors.push(e); continue; }
        };
        let ty_ctor = match dty.leftmost_symbol()
        {
            Some(&Prefix::User(s)) => s,
            Some(&Prefix::Arrow(p)) => { errors.place_back() <- ConstructorCollectionError::ArrowNotAllowed(p); continue; },
            Some(&Prefix::PathRef(ref p, _)) => { errors.place_back() <- ConstructorCollectionError::PathRefNotAllowed(p.position()); continue; },
            None => { errors.place_back() <- ConstructorCollectionError::ConstructorNotFound(dty.position()); continue; }
        };
        // println!("**dbg** Found Type Constructor: {:?}", ty_ctor);
        let mut dcons: Vec<_> = defs.iter().map(|dc| &dc.name).collect();
        // println!("**dbg** Found Data Constructor for {:?} = {:?}", ty_ctor, dcons);

        env.symbol_set_mut().ty.insert(ty_ctor);
        env.symbol_set_mut().data.entry(ty_ctor).or_insert(Vec::new()).append(&mut dcons);
    }
    for &(ref tys, _) in tree.type_fns().iter().flat_map(|tf| &tf.defs)
    {
        let dty = match deform_ty(tys, &aenv).map_err(ConstructorCollectionError::DeformingError)
        {
            Ok(t) => t, Err(e) => { errors.push(e); continue; }
        };
        let ty_ctor = match dty.leftmost_symbol()
        {
            Some(&Prefix::User(ref s)) => s,
            Some(&Prefix::Arrow(p)) => { errors.place_back() <- ConstructorCollectionError::ArrowNotAllowed(p); continue; },
            Some(&Prefix::PathRef(ref p, _)) => { errors.place_back() <- ConstructorCollectionError::PathRefNotAllowed(p.position()); continue; },
            None => { errors.place_back() <- ConstructorCollectionError::ConstructorNotFound(dty.position()); continue; }
        };
        // println!("**dbg** Found Type Constructor: {:?}", ty_ctor);
        env.symbol_set_mut().ty.insert(ty_ctor);
    }
    if errors.is_empty() { Ok(()) } else { Err(errors) }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Prefix<'s: 't, 't> { Arrow(&'t Location), User(&'t Source<'s>), PathRef(Box<TyDeformerIntermediate<'s, 't>>, Vec<&'t Source<'s>>) }
impl<'s: 't, 't> Prefix<'s, 't>
{
    pub fn is_equal_nolocation(&self, other: &Self) -> bool
    {
        match *self
        {
            Prefix::Arrow(p) => *other == Prefix::Arrow(p),
            Prefix::User(&Source { slice, .. }) => if let Prefix::User(&Source { slice: slice_, .. }) = *other { slice == slice_ } else { false },
            Prefix::PathRef(ref p, ref v) => if let Prefix::PathRef(ref p_, ref v_) = *other
            {
                p.is_equal_nolocation(&p_) && v.len() == v_.len() && v.iter().zip(v_.iter()).all(|(a, b)| a.slice == b.slice)
            }
            else { false }
        }
    }
    pub fn position(&self) -> &'t Location
    {
        match *self
        {
            Prefix::Arrow(p) => p, Prefix::User(&Source { pos: ref p, .. }) => p, Prefix::PathRef(ref p, _) => p.position()
        }
    }
}
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TyDeformerIntermediate<'s: 't, 't>
{
    Placeholder(&'t Location), Expressed(Prefix<'s, 't>, Vec<TyDeformerIntermediate<'s, 't>>),
    SafetyGarbage, Basic(&'t Location, BType), Tuple(&'t Location, Vec<TyDeformerIntermediate<'s, 't>>),
    ArrayDim(Box<TyDeformerIntermediate<'s, 't>>, &'t InferredArrayDim<'s>)
}
impl<'s: 't, 't> TyDeformerIntermediate<'s, 't>
{
    pub fn position(&self) -> &'t Location
    {
        match *self
        {
            TyDeformerIntermediate::Placeholder(p) | TyDeformerIntermediate::Tuple(p, _) => p,
            TyDeformerIntermediate::Expressed(ref p, _) => p.position(),
            TyDeformerIntermediate::ArrayDim(ref p, _) => p.position(),
            _ => unreachable!()
        }
    }
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
    pub fn leftmost_symbol(&self) -> Option<&Prefix<'s, 't>>
    {
        match *self
        {
            TyDeformerIntermediate::Expressed(ref p, _) => Some(p), _ => None
        }
    }
}

#[derive(Debug)] pub enum DeformationError<'t>
{
    ArgumentRequired(&'t Location), UnresolvedAssociation(&'t Location), ConstructorRequired(&'t Location),
    ApplicationProhibited(&'t Location)
}
/// Deforming(Resolving infix operators to prefix style) a TypeSynTree using current AssociativityEnv
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
        TypeSynTree::ArrowInfix { ref op_pos, ref lhs, ref rhs } => Ok(TyDeformerIntermediate::Expressed(Prefix::Arrow(op_pos), vec![
            deform_ty(lhs, assoc_env)?, deform_ty(rhs, assoc_env)?
        ])),
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
