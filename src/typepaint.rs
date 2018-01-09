//! Type Painter

use std::collections::HashSet;
use std::rc::Rc;
use super::parser::*;
use super::Location;
use std::ops::DerefMut;
use deformer::*;
use {RcMut, WeakMut, new_rcmut};

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

/// Common DataStore for Constructor Environment
pub struct ConstructorEnv<'s: 't, 't>
{
    pub ty: HashSet<GenSource<'s, 't>>, pub data: Vec<TypedDataConstructorScope<'s, 't>>
}
impl<'s: 't, 't> ConstructorEnv<'s, 't>
{
    fn new() -> Self { ConstructorEnv { ty: HashSet::new(), data: Vec::new() } }
    fn is_empty(&self) -> bool { self.ty.is_empty() && self.data.is_empty() }
}
/// Indicates the type that constructs a Construct Environment.
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
    DeformingError(DeformationError<'t>), ConstructorNotFound(&'t Location), ArrowNotAllowed(&'t Location), PathRefNotAllowed(&'t Location),
    InvalidConstructor(&'t Location)
}
impl<'t> From<DeformationError<'t>> for ConstructorCollectionError<'t>
{
    fn from(t: DeformationError<'t>) -> Self { ConstructorCollectionError::DeformingError(t) }
}

#[derive(Debug)]
pub struct TypedDataConstructorScope<'s: 't, 't>
{
    pub name: GenSource<'s, 't>, pub ty: TyDeformerIntermediate<'s, 't>,
    pub ctors: Vec<TypedDataConstructor<'s, 't>>
}
#[derive(Debug)]
pub struct TypedDataConstructor<'s: 't, 't>
{
    pub name: GenSource<'s, 't>, pub param_count: usize,
    pub ty: TyDeformerIntermediate<'s, 't>, pub expressed: ::Lambda<'s, 't>
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

pub trait ConstructorCollector<'s: 't, 't>
{
    type Env: 't;
    fn collect_ctors(&'t self, env: &RcMut<Self::Env>) -> Result<(), Vec<ConstructorCollectionError<'t>>>;
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
    fn collect_ctors(&'t self, env: &RcMut<Self::Env>) -> Result<(), Vec<ConstructorCollectionError>>
    {
        collect_for_type_decls(env.borrow_mut().deref_mut(), self)
    }
}
macro_rules! CollectErrors
{
    { $e: expr =>? $collector: expr; continue } => { match $e { Err(e) => { $collector.push(e.into()); continue; }, Ok(v) => v } };
    { $e: expr =>? $collector: expr; continue $lp: tt } => { match $e { Err(e) => { $collector.push(e.into()); continue $lp; }, Ok(v) => v } };
    { $e: expr =>[?] $collector: expr; continue } => { match $e { Err(e) => { $collector.append(&mut e.into_iter().map(From::from).collect()); continue; }, Ok(v) => v } };
}
struct DeformedDataConstructor<'s: 't, 't> { pub name: GenSource<'s, 't>, args: Vec<GenSource<'s, 't>> }
impl<'s: 't, 't> DeformedDataConstructor<'s, 't>
{
    pub fn from_ir(ir: &TyDeformerIntermediate<'s, 't>) -> Result<Self, &'t Location>
    {
        if let TyDeformerIntermediate::Expressed(Prefix::User(ref name), ref args) = *ir
        {
            let mut c = DeformedDataConstructor { name: name.clone(), args: Vec::with_capacity(args.len()) };
            for a in args
            {
                if let TyDeformerIntermediate::Expressed(Prefix::User(ref arg), ref v) = *a
                {
                    if v.is_empty() { c.args.push(arg.clone()); continue; }
                }
                return Err(a.position());
            }
            Ok(c)
        }
        else { Err(ir.position()) }
    }
}
fn generate_ctor_arrows<'s: 't, 't>(ctors: &[DeformedDataConstructor<'s, 't>], cont_placeholder: &TyDeformerIntermediate<'s, 't>)
    -> TyDeformerIntermediate<'s, 't>
{
    ctors.iter().map(|&DeformedDataConstructor { ref args, .. }|
    {
        // 個別のコンストラクタについて、a -> b -> rの形を作る
        args.iter().cloned().map(TyDeformerIntermediate::symref).rev().fold(cont_placeholder.clone(), |t, a| a.arrow(t))
    }).rev().fold(cont_placeholder.clone(), |t, ct| ct.arrow(t))
    // 最後に(a -> r) -> (b -> r) -> rの形にまとめる
}
fn express_ctor<'s: 't, 't>(ctor: &DeformedDataConstructor<'s, 't>, selector: &GenSource<'s, 't>, ctor_fns: &[GenSource<'s, 't>]) -> ::Lambda<'s, 't>
{
    // 最終型(f0 a b)の形にする
    let xf = ctor.args.iter().cloned().fold(::Lambda::SymRef(selector.clone()), |x, a| x.apply(::Lambda::SymRef(a)));
    // 継続の受け付け束縛、そのあとコンストラクタ引数を追加する
    ctor_fns.iter().chain(&ctor.args).cloned().rev().fold(xf, |x, a| ::Lambda::Fun { arg: a, expr: box x })
}
fn collect_for_type_decls<'s: 't, 't, Env, T>(env: &mut Env, tree: &'t T) -> Result<(), Vec<ConstructorCollectionError<'t>>>
    where Env: ConstructorEnvironment<'s, 't>, T: TypeDeclarable<'s> + AssociativityEnvironment<'s>
{
    let aenv = tree.assoc_env().borrow();
    let mut errors = Vec::new();
    for &(ref ty, ref defs) in tree.type_decls().iter().flat_map(|td| &td.defs)
    {
        let dty = CollectErrors!{ deform_ty(ty, &aenv) =>? errors; continue };
        let ty_ctor_name = match dty.leftmost_symbol()
        {
            Some(&Prefix::User(ref s)) => s,
            Some(&Prefix::Arrow(p)) => { errors.place_back() <- ConstructorCollectionError::ArrowNotAllowed(p); continue; },
            Some(&Prefix::PathRef(ref p, _)) => { errors.place_back() <- ConstructorCollectionError::PathRefNotAllowed(p.position()); continue; },
            None => { errors.place_back() <- ConstructorCollectionError::ConstructorNotFound(dty.position()); continue; }
        };
        let mut deformed_ctors = Vec::with_capacity(defs.len());
        for &DataConstructor { ref tree, .. } in defs
        {
            let deformed = CollectErrors!{ deform_ty(tree, &aenv) =>? errors; continue };
            deformed_ctors.place_back() <- CollectErrors!{
                DeformedDataConstructor::from_ir(&deformed).map_err(ConstructorCollectionError::InvalidConstructor) =>? errors; continue
            };
        }
        let cont_placeholder_ty = TyDeformerIntermediate::symref(GenSource::Generated("r".into()));
        let cont_placeholders_fn: Vec<_> = (0 .. deformed_ctors.len()).map(|n| GenSource::Generated(format!("f{}", n))).collect();

        let cont_arrow_tys = generate_ctor_arrows(&deformed_ctors, &cont_placeholder_ty);
        let dcons: Vec<_> = deformed_ctors.into_iter().zip(&cont_placeholders_fn).map(|(ctor, cfn)| TypedDataConstructor
        {
            param_count: ctor.args.len(), ty: dcons_ty(&ctor, &dty), expressed: express_ctor(&ctor, cfn, &cont_placeholders_fn), name: ctor.name
        }).collect();
        // println!("**dbg** Found Type Constructor: {:?}", ty_ctor);
        // println!("**dbg** Found Data Constructor for {:?} = {:?}", ty_ctor, dcons);

        env.symbol_set_mut().ty.insert(ty_ctor_name.clone());
        env.symbol_set_mut().data.place_back() <- TypedDataConstructorScope { name: ty_ctor_name.clone(), ty: cont_arrow_tys, ctors: dcons };
    }
    for &(ref tys, _) in tree.type_fns().iter().flat_map(|tf| &tf.defs)
    {
        let dty = match deform_ty(tys, &aenv).map_err(ConstructorCollectionError::DeformingError)
        {
            Ok(t) => t, Err(e) => { errors.push(e); continue; }
        };
        let ty_ctor = match dty.leftmost_symbol()
        {
            Some(&Prefix::User(ref s)) => s.clone(),
            Some(&Prefix::Arrow(p)) => { errors.place_back() <- ConstructorCollectionError::ArrowNotAllowed(p); continue; },
            Some(&Prefix::PathRef(ref p, _)) => { errors.place_back() <- ConstructorCollectionError::PathRefNotAllowed(p.position()); continue; },
            None => { errors.place_back() <- ConstructorCollectionError::ConstructorNotFound(dty.position()); continue; }
        };
        // println!("**dbg** Found Type Constructor: {:?}", ty_ctor);
        env.symbol_set_mut().ty.insert(ty_ctor);
    }
    if errors.is_empty() { Ok(()) } else { Err(errors) }
}

/// データコンストラクタの型の抽出 今回はGADTsは考慮しない
/// Ctor a :: a -> Data a
fn dcons_ty<'s: 't, 't>(dtree: &DeformedDataConstructor<'s, 't>, data_ty: &TyDeformerIntermediate<'s, 't>) -> TyDeformerIntermediate<'s, 't>
{
    dtree.args.iter().cloned().rev().fold(data_ty.clone(), |t, a| TyDeformerIntermediate::symref(a).arrow(t))
}

/// カインド型
pub enum TyConsKind { Star, Arrow(Box<TyConsKind>, Box<TyConsKind>), Constraint }

#[cfg(test)]
mod test
{
    use deformer::{GenSource, TyDeformerIntermediate, Prefix, EqNoloc};
    use std::str::from_utf8;

    #[test] fn dcons_ty()
    {
        let ctor = super::DeformedDataConstructor { name: GenSource::Generated("Ctor".to_string()), args: vec![GenSource::Generated("a".to_string())] };
        let final_ty = TyDeformerIntermediate::Expressed(Prefix::User(GenSource::Generated("Data".to_string())),
            vec![TyDeformerIntermediate::symref(GenSource::Generated("a".to_string()))]);
        let r = super::dcons_ty(&ctor, &final_ty);
        assert!(r.eq_nolocation(&TyDeformerIntermediate::symref(GenSource::Generated("a".to_string())).arrow(final_ty.clone())));
    }
    #[test] fn generate_ctor_arrows()
    {
        let ctors = vec![
            super::DeformedDataConstructor { name: GenSource::Generated("Ok".to_string()), args: vec![GenSource::Generated("t".to_string())] },
            super::DeformedDataConstructor { name: GenSource::Generated("Err".to_string()), args: vec![GenSource::Generated("e".to_string())] },
            super::DeformedDataConstructor { name: GenSource::Generated("Void".to_string()), args: Vec::new() }
        ];
        let cont_placeholder = TyDeformerIntermediate::symref(GenSource::Generated("r".to_string()));
        let r = super::generate_ctor_arrows(&ctors, &cont_placeholder);

        let ok_arrow = TyDeformerIntermediate::symref(GenSource::Generated("t".to_string())).arrow(cont_placeholder.clone());
        let err_arrow = TyDeformerIntermediate::symref(GenSource::Generated("e".to_string())).arrow(cont_placeholder.clone());
        let rsuc = ok_arrow.arrow(err_arrow.arrow(cont_placeholder.clone().arrow(cont_placeholder.clone())));
        let mut s = Vec::new(); r.pretty_print(&mut s).unwrap();
        let mut s2 = Vec::new(); rsuc.pretty_print(&mut s2).unwrap();
        assert!(r.eq_nolocation(&rsuc), "result: {} <=> {}", from_utf8(&s).unwrap(), from_utf8(&s2).unwrap());
    }
}

// paint
// matf a b => matf(constructor) a(tyvar) b(tyvar)
// (X _) -> Int => (->) (X _) Int => (->) (forall t0. X t0) Int または forall t0. (->) (X t0) Int
// (X _)[] -> Int => (->) [X _] Int => (->) [forall t0. X t0] Int (forall t0. (->) [X t0] Intとすると意味が変わる)

// pub fn quantize_ty<'s: 't, 't>(tree: &TyDeformerIntermediate<'s, 't>) -> 

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

