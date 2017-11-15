//! Type Painter

use std::collections::{HashMap, HashSet};
use typeparser::{TypeFragment, Type};
use std::rc::{Rc, Weak};

/// 結合方向と強度
pub enum Associativity { Left(usize), Right(usize), None(usize) }
/// ローカル優先結合指定
pub struct AssociativityEnv<'s>
{
    pub ops: HashMap<&'s str, Associativity>,
    pub children: Vec<AssociativityEnv<'s>>
}
pub trait AssociativityCollector<'s>
{
    fn collect_assoc(&self, scope: &mut AssociativityEnv<'s>);
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
pub struct PaintedTypeString<'s>(Vec<PaintedType<'s>>);
