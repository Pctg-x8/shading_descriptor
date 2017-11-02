//! Type Painter

use std::collections::{HashMap, HashSet};
use typeparser::{TypeFragment, Type};
use std::rc::{Rc, Weak};

pub struct TyConstructorEnv<'s>
{
    pub constructors: HashSet<&'s str>, pub children: Vec<TyConstructorEnv<'s>>
}
impl<'s> TyConstructorEnv<'s>
{
    pub fn collect(syn: &Type<'s>, )
}

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
pub struct PaintedTypeString<'s>(Vec<PaintedType<'s>>)
