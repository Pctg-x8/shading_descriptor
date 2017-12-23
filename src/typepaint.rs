//! Type Painter

use std::collections::{HashMap, HashSet};
use std::rc::{Rc, Weak};

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
