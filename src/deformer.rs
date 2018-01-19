
use {Location, Source, GenSource, BType, Associativity, AssociativityEnv, GenNumeric};
use {TypeSynTree, InferredArrayDim};
use std::mem::replace;
use std::ops::Deref;
use parser;
use std::result::Result as StdResult;

#[derive(Debug, Clone)] pub enum DeformationError
{
    ArgumentRequired(Location), UnresolvedAssociation(Location), ConstructorRequired(Location),
    ApplicationProhibited(Location), UnableToApply(Location)
}
pub type Result<T> = StdResult<T, DeformationError>;
pub trait Deformable<'s: 't, 't>
{
    type Deformed: 't;
    fn deform(&'t self, assoc: &AssociativityEnv<'s>) -> Result<Self::Deformed>;
}
/// Multiple deformation with same associativity environment
impl<'s: 't, 't, T: Deformable<'s, 't>> Deformable<'s, 't> for [T]
{
    type Deformed = Vec<<T as Deformable<'s, 't>>::Deformed>;
    fn deform(&'t self, assoc: &AssociativityEnv<'s>) -> Result<Self::Deformed> { self.iter().map(|x| x.deform(assoc)).collect() }
}
/// Pair deformation with same associatiivty environment
impl<'s: 't, 't, A: Deformable<'s, 't>, B: Deformable<'s, 't>> Deformable<'s, 't> for (A, B)
{
    type Deformed = (<A as Deformable<'s, 't>>::Deformed, <B as Deformable<'s, 't>>::Deformed);
    fn deform(&'t self, assoc: &AssociativityEnv<'s>) -> Result<Self::Deformed> { Ok((self.0.deform(assoc)?, self.1.deform(assoc)?)) }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Prefix<'s: 't, 't> { Arrow(&'t Location), User(GenSource<'s, 't>), PathRef(Box<Ty<'s, 't>>, Vec<GenSource<'s, 't>>) }
impl<'s: 't, 't> Prefix<'s, 't>
{
    pub fn position(&self) -> &Location
    {
        match *self
        {
            Prefix::Arrow(p) => p, Prefix::User(ref s) => s.position(), Prefix::PathRef(ref p, _) => p.position()
        }
    }
}
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SymPath<'s: 't, 't> { pub base: GenSource<'s, 't>, pub desc: Vec<GenSource<'s, 't>> }
impl<'s: 't, 't> SymPath<'s, 't> { pub fn position(&self) -> &Location { self.base.position() } }

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Ty<'s: 't, 't>
{
    Placeholder(&'t Location), Expressed(Prefix<'s, 't>, Vec<Ty<'s, 't>>),
    SafetyGarbage, Basic(&'t Location, BType), Tuple(&'t Location, Vec<Ty<'s, 't>>),
    ArrayDim(Box<Ty<'s, 't>>, &'t InferredArrayDim<'s>)
}
/// forall (quanitified...). constraints => def
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FullTy<'s: 't, 't>
{
    pub quantified: Vec<GenSource<'s, 't>>, pub constraints: Vec<Ty<'s, 't>>, pub def: Ty<'s, 't>
}
impl<'s: 't, 't> Ty<'s, 't>
{
    pub fn position(&self) -> &Location
    {
        match *self
        {
            Ty::Placeholder(p) | Ty::Tuple(p, _) | Ty::Basic(p, _) => p,
            Ty::Expressed(ref p, _) => p.position(),
            Ty::ArrayDim(ref p, _) => p.position(),
            Ty::SafetyGarbage => unreachable!("internal garbage item")
        }
    }
}

pub struct InfixIntermediate<'s: 't, 't, IR: 't> { op: &'t Source<'s>, assoc: Associativity, ir: IR }
impl<'s: 't, 't> Ty<'s, 't>
{
    /// self <+> (new_lhs new_arg) = (new_lhs self new_arg)
    fn combine(self, new_lhs: Prefix<'s, 't>, new_arg: Self) -> Self
    {
        Ty::Expressed(new_lhs, vec![self, new_arg])
    }
    fn combine_inplace(&mut self, new_lhs: Prefix<'s, 't>, new_arg: Self) -> &mut Self
    {
        let old = replace(self, Ty::SafetyGarbage);
        *self = old.combine(new_lhs, new_arg); self
    }
    fn append_args(&mut self, new_args: &mut Vec<Self>)
    {
        match *self
        {
            Ty::Expressed(_, ref mut args) => args.append(new_args),
            _ => unreachable!("{:?}", self)
        }
    }

    /// self -> x
    pub fn arrow(self, x: Self) -> Self { Ty::Expressed(Prefix::Arrow(&Location::EMPTY), vec![self, x]) }
    /// x
    pub fn symref(x: GenSource<'s, 't>) -> Self { Ty::Expressed(Prefix::User(x), Vec::new()) }

    pub fn leftmost_symbol(&self) -> Option<&Prefix<'s, 't>>
    {
        match *self
        {
            Ty::Expressed(ref p, _) => Some(p), _ => None
        }
    }
}
impl<'s: 't, 't> EqNoloc for Ty<'s, 't>
{
    fn eq_nolocation(&self, other: &Self) -> bool
    {
        match *self
        {
            Ty::Placeholder(_) => if let Ty::Placeholder(_) = *other { true } else { false },
            Ty::Expressed(ref p, ref v) =>
                if let Ty::Expressed(ref p_, ref v_) = *other { p.eq_nolocation(p_) && v.eq_nolocation(v_) } else { false },
            Ty::SafetyGarbage => unreachable!(),
            Ty::Basic(_, bt) => if let Ty::Basic(_, bt_) = *other { bt == bt_ } else { false },
            Ty::Tuple(_, ref v) => if let Ty::Tuple(_, ref v_) = *other { v.eq_nolocation(v_) } else { false },
            Ty::ArrayDim(ref p, ref e) => if let Ty::ArrayDim(ref p_, ref e_) = *other
            {
                p.eq_nolocation(p_) && e == e_
            }
            else { false }
        }
    }
}
impl<'s: 't, 't> EqNoloc for Prefix<'s, 't>
{
    fn eq_nolocation(&self, other: &Self) -> bool
    {
        match *self
        {
            Prefix::Arrow(p) => *other == Prefix::Arrow(p),
            Prefix::User(ref s) => if let Prefix::User(ref s_) = *other { s.text() == s_.text() } else { false },
            Prefix::PathRef(ref p, ref v) => if let Prefix::PathRef(ref p_, ref v_) = *other { p.eq_nolocation(&p_) && v.eq_nolocation(v_) } else { false }
        }
    }
}

/// Deforming(Resolving infix operators to prefix style) a TypeSynTree using current AssociativityEnv
impl<'s: 't, 't> Deformable<'s, 't> for TypeSynTree<'s>
{
    type Deformed = Ty<'s, 't>;
    fn deform(&'t self, assoc_env: &AssociativityEnv<'s>) -> Result<Self::Deformed>
    {
        use TypeSynTree::*; use self::Prefix as PrefixKind;
        match *self
        {
            // a b... => (deform(a), sym_placeholder(b...))
            Prefix(ref v1, ref vs) =>
            {
                let mut lhs = v1.deform(assoc_env)?;
                lhs.append_args(&mut vs.deform(assoc_env)?);
                Ok(lhs)
            },
            Infix { ref lhs, ref mods } =>
            {
                let mut mods: Vec<_> = mods.iter().map(|&(ref op, ref rhs)| Ok(InfixIntermediate
                {
                    op, assoc: assoc_env.lookup(op.slice), ir: rhs.deform(assoc_env)?
                })).collect::<Result<_>>()?;
                let mut lhs = lhs.deform(assoc_env)?;
                while !mods.is_empty()
                {
                    let agg = extract_most_precedences(&mods).map_err(|p| DeformationError::UnresolvedAssociation(p.clone()))?.unwrap();
                    let ir = mods.remove(agg.index);
                    let cell = if agg.index >= 1 { &mut mods[agg.index - 1].ir } else { &mut lhs };
                    cell.combine_inplace(PrefixKind::User(ir.op.into()), ir.ir);
                }
                Ok(lhs)
            },
            // a => a, []
            SymReference(ref sym) => Ok(Ty::symref(sym.into())),
            PathRef(ref base, ref v) => Ok(Ty::Expressed(PrefixKind::PathRef(box base.deform(assoc_env)?, v.iter().map(GenSource::from).collect()), Vec::new())),
            Placeholder(ref p) => Ok(Ty::Placeholder(p)),
            Basic(ref p, bt) => Ok(Ty::Basic(p, bt)),
            Tuple(ref p, ref v) => Ok(Ty::Tuple(p, v.deform(assoc_env)?)),
            ArrowInfix { ref op_pos, ref lhs, ref rhs } => Ok(Ty::Expressed(PrefixKind::Arrow(op_pos), vec![lhs.deform(assoc_env)?, rhs.deform(assoc_env)?])),
            ArrayDim { ref lhs, ref num } => Ok(Ty::ArrayDim(box lhs.deform(assoc_env)?, num))
        }
    }
}
impl<'s: 't, 't> Deformable<'s, 't> for parser::FullTypeDesc<'s>
{
    type Deformed = FullTy<'s, 't>;
    fn deform(&'t self, assoc_env: &AssociativityEnv<'s>) -> Result<Self::Deformed>
    {
        let constraints = self.constraints.iter().map(|c| c.deform(assoc_env)).collect::<Result<_>>()?;
        Ok(FullTy { quantified: self.quantified.iter().map(From::from).collect(), constraints, def: self.tree.deform(assoc_env)? })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding<'s: 't, 't> { pub pat: ExprPat<'s, 't>, pub expr: Expr<'s, 't> }

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockContent<'s: 't, 't> { Vars(Vec<Binding<'s, 't>>), Expr(Expr<'s, 't>) }
impl<'s: 't, 't> From<Vec<Binding<'s, 't>>> for BlockContent<'s, 't> { fn from(v: Vec<Binding<'s, 't>>) -> Self { BlockContent::Vars(v) } }
impl<'s: 't, 't> From<Expr<'s, 't>> for BlockContent<'s, 't> { fn from(v: Expr<'s, 't>) -> Self { BlockContent::Expr(v) } }
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr<'s: 't, 't>
{
    Garbage,
    Apply(GenSource<'s, 't>, Vec<Expr<'s, 't>>), Numeric(GenNumeric<'s, 't>),
    ArrayLiteral(&'t Location, Vec<Expr<'s, 't>>),
    ArrayRef(Box<Expr<'s, 't>>, Box<Expr<'s, 't>>),
    PathRef(Box<Expr<'s, 't>>, Vec<GenSource<'s, 't>>),
    Unit(&'t Location), Tuple1(Box<Expr<'s, 't>>, Vec<Expr<'s, 't>>),
    // full //
    Conditional
    {
        head: &'t Location, cond: Box<Expr<'s, 't>>, then: Box<Expr<'s, 't>>, else_: Option<Box<Expr<'s, 't>>>
    },
    Block(&'t Location, Vec<BlockContent<'s, 't>>),
    Lettings { head: &'t Location, vars: Vec<Binding<'s, 't>>, subexpr: Box<Expr<'s, 't>> },
    CaseOf { head: &'t Location, expr: Box<Expr<'s, 't>>, matchers: Vec<(ExprPat<'s, 't>, Expr<'s, 't>)> }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprPat<'s: 't, 't>
{
    Garbage, SymBinding(GenSource<'s, 't>), Numeric(GenNumeric<'s, 't>), PathRef(GenSource<'s, 't>, Vec<GenSource<'s, 't>>),
    ArrayLiteral(&'t Location, Vec<ExprPat<'s, 't>>), Unit(&'t Location), Tuple(Box<ExprPat<'s, 't>>, Vec<ExprPat<'s, 't>>),
    Apply(SymPath<'s, 't>, Vec<ExprPat<'s, 't>>), Placeholder(&'t Location)
}
impl<'s: 't, 't> Expr<'s, 't>
{
    fn assume_application(&self) -> StdResult<&Self, &Self>
    {
        if let Expr::Apply(_, _) = *self { Ok(self) } else { Err(self) }
    }
    fn append_args(&mut self, args: &mut Vec<Self>)
    {
        if let Expr::Apply(_, ref mut a) = *self { a.append(args); }
        else { unreachable!("invalid usage") }
    }
    fn combine(self, new_lhs: GenSource<'s, 't>, new_arg: Self) -> Self
    {
        Expr::Apply(new_lhs, vec![self, new_arg])
    }
    fn combine_inplace(&mut self, new_lhs: GenSource<'s, 't>, new_arg: Self)
    {
        let old = replace(self, Expr::Garbage);
        *self = old.combine(new_lhs, new_arg);
    }

    pub fn position(&self) -> &Location
    {
        match *self
        {
            Expr::Garbage => unreachable!(),
            Expr::Apply(ref s, _) => s.position(),
            Expr::Numeric(ref n) => n.position(),
            Expr::ArrayLiteral(p, _) | Expr::Unit(p) => p,
            Expr::ArrayRef(ref x, _) | Expr::PathRef(ref x, _) | Expr::Tuple1(ref x, _) => x.position(),
            Expr::Conditional { head, .. } | Expr::Lettings { head, .. } | Expr::Block(head, ..) |
            Expr::CaseOf { head, .. } => head
        }
    }
}
impl<'s: 't, 't> ExprPat<'s, 't>
{
    pub fn position(&self) -> &Location
    {
        match *self
        {
            ExprPat::SymBinding(ref s) | ExprPat::PathRef(ref s, ..) => s.position(),
            ExprPat::ArrayLiteral(ref p, _) | ExprPat::Unit(ref p) | ExprPat::Placeholder(ref p) => p,
            ExprPat::Numeric(ref n) => n.position(),
            ExprPat::Apply(ref p0, _) => p0.position(), ExprPat::Tuple(ref p0, _) => p0.position(),
            ExprPat::Garbage => unreachable!("internal garbage")
        }
    }
}
pub trait EqNoloc { fn eq_nolocation(&self, other: &Self) -> bool; }
/// and
impl<A: EqNoloc, B: EqNoloc> EqNoloc for (A, B)
{
    fn eq_nolocation(&self, other: &(A, B)) -> bool { self.0.eq_nolocation(&other.0) && self.1.eq_nolocation(&other.1) }
}
/// all
impl<T: EqNoloc> EqNoloc for [T]
{
    fn eq_nolocation(&self, other: &[T]) -> bool { self.len() == other.len() && self.iter().zip(other.iter()).all(|(a, b)| a.eq_nolocation(b)) }
}
impl<T: EqNoloc> EqNoloc for Option<T>
{
    fn eq_nolocation(&self, other: &Option<T>) -> bool { self.as_ref().map_or(other.is_none(), |a| other.as_ref().map_or(false, |b| a.eq_nolocation(b))) }
}
impl<T: EqNoloc> EqNoloc for Box<T> { fn eq_nolocation(&self, other: &Box<T>) -> bool { self.deref().eq_nolocation(other.deref()) } }
impl<'s> EqNoloc for Source<'s> { fn eq_nolocation(&self, other: &Self) -> bool { self.slice == other.slice } }
impl<'s: 't, 't> EqNoloc for &'t Source<'s> { fn eq_nolocation(&self, other: &Self) -> bool { self.slice == other.slice } }
impl<'s: 't, 't> EqNoloc for Expr<'s, 't>
{
    fn eq_nolocation(&self, other: &Self) -> bool
    {
        match *self
        {
            Expr::Garbage => false,
            Expr::Apply(ref s, ref v) =>
                if let Expr::Apply(ref s_, ref v_) = *other { s.text() == s_.text() && v.eq_nolocation(v_) } else { false },
            Expr::Numeric(ref n) => if let Expr::Numeric(ref n_) = *other { n.eq_nolocation(n_) } else { false },
            Expr::ArrayLiteral(_, ref v) => if let Expr::ArrayLiteral(_, ref v_) = *other { v.eq_nolocation(v_) } else { false },
            Expr::Tuple1(ref x, ref v) => if let Expr::Tuple1(ref x_, ref v_) = *other
            {
                x.eq_nolocation(x_) && v.eq_nolocation(v_)
            }
            else { false },
            Expr::Unit(_) => if let Expr::Unit(_) = *other { true } else { false },
            Expr::ArrayRef(ref b, ref x) =>
                if let Expr::ArrayRef(ref b_, ref x_) = *other { b.eq_nolocation(b_) && x.eq_nolocation(x_) } else { false },
            Expr::PathRef(ref b, ref v) =>
                if let Expr::PathRef(ref b_, ref v_) = *other { b.eq_nolocation(b_) && v.eq_nolocation(v_) } else { false },
            Expr::Conditional { ref cond, ref then, ref else_, .. } =>
                if let Expr::Conditional { cond: ref cond_, then: ref then_, else_: ref else__, .. } = *other
                {
                    cond.eq_nolocation(cond_) && then.eq_nolocation(then_) && else_.eq_nolocation(else__)
                }
                else { false },
            Expr::Block(_, ref v) => if let Expr::Block(_, ref v_) = *other { v.eq_nolocation(v_) } else { false },
            Expr::Lettings { ref vars, ref subexpr, .. } =>
                if let Expr::Lettings { vars: ref vars_, subexpr: ref subexpr_, .. } = *other
                {
                    vars.eq_nolocation(vars_) && subexpr.eq_nolocation(subexpr_)
                }
                else { false },
            Expr::CaseOf { ref expr, ref matchers, .. } =>
                if let Expr::CaseOf { expr: ref expr_, matchers: ref matchers_, .. } = *other
                {
                    expr.eq_nolocation(expr_) && matchers.eq_nolocation(matchers_)
                }
                else { false }
        }
    }
}
impl<'s: 't, 't> EqNoloc for BlockContent<'s, 't>
{
    fn eq_nolocation(&self, other: &Self) -> bool
    {
        match *self
        {
            BlockContent::Vars(ref v) => if let BlockContent::Vars(ref v_) = *other { v.eq_nolocation(v_) } else { false },
            BlockContent::Expr(ref x) => if let BlockContent::Expr(ref x_) = *other { x.eq_nolocation(x_) } else { false }
        }
    }
}
impl<'s: 't, 't> EqNoloc for Binding<'s, 't>
{
    fn eq_nolocation(&self, other: &Self) -> bool { self.pat.eq_nolocation(&other.pat) && self.expr.eq_nolocation(&other.expr) }
}
impl<'s: 't, 't> Deformable<'s, 't> for parser::ExpressionSynTree<'s>
{
    type Deformed = Expr<'s, 't>;
    fn deform(&'t self, assoc_env: &AssociativityEnv<'s>) -> Result<Self::Deformed>
    {
        use parser::ExpressionSynTree::*;
        match *self
        {
            Prefix(ref v0, ref v) =>
            {
                let mut lhs = v0.deform(assoc_env)?;
                lhs.assume_application().map_err(|lhs| DeformationError::UnableToApply(lhs.position().clone()))?;
                lhs.append_args(&mut v.deform(assoc_env)?);
                Ok(lhs)
            },
            Infix { ref lhs, ref mods } =>
            {
                let mut mods: Vec<_> = mods.iter().map(|&(ref op, ref rhs)| Ok(InfixIntermediate
                {
                    op, assoc: assoc_env.lookup(op.slice), ir: rhs.deform(assoc_env)?
                })).collect::<Result<_>>()?;
                let mut lhs = lhs.deform(assoc_env)?;
                while !mods.is_empty()
                {
                    let agg = extract_most_precedences(&mods).map_err(|p| DeformationError::UnresolvedAssociation(p.clone()))?.unwrap();
                    let ir = mods.remove(agg.index);
                    let cell = if agg.index >= 1 { &mut mods[agg.index - 1].ir } else { &mut lhs };
                    cell.combine_inplace(GenSource::Sliced(&ir.op), ir.ir);
                }
                Ok(lhs)
            },
            SymReference(ref s) => Ok(Expr::Apply(GenSource::Sliced(s), Vec::new())),
            Numeric(ref s) => Ok(Expr::Numeric(s.into())),
            ArrayLiteral(ref p, ref a) => Ok(Expr::ArrayLiteral(p, a.deform(assoc_env)?)),
            Tuple(ref p, ref a) => if let Some(a1) = a.first() { Ok(Expr::Tuple1(box a1.deform(assoc_env)?, a.deform(assoc_env)?)) } else { Ok(Expr::Unit(p)) },
            ArrayRef(ref base, ref index) => Ok(Expr::ArrayRef(box base.deform(assoc_env)?, box index.deform(assoc_env)?)),
            RefPath(ref base, ref path) => Ok(Expr::PathRef(box base.deform(assoc_env)?, path.iter().map(From::from).collect()))
        }
    }
}
impl<'s: 't, 't> Deformable<'s, 't> for parser::FullExpression<'s>
{
    type Deformed = Expr<'s, 't>;
    fn deform(&'t self, assoc_env: &AssociativityEnv<'s>) -> Result<Self::Deformed>
    {
        use parser::FullExpression::*;
        match *self
        {
            Expression(ref e) => e.deform(assoc_env),
            Conditional { ref location, inv, ref cond, ref then, ref else_ } =>
            {
                let mut cond = cond.deform(assoc_env)?;
                if inv { cond = Expr::Apply(GenSource::Sliced(&NOT_TOKEN), vec![cond]); }
                let (then, else_) = (then.deform(assoc_env)?, reverse_opt_res(else_.as_ref().map(|e| e.deform(assoc_env)))?);
                Ok(Expr::Conditional { head: location, cond: box cond, then: box then, else_: else_.map(Box::new) })
            },
            Block(ref p, ref elist) => elist.iter().map(|x| match *x
            {
                parser::BlockContent::BlockVars { ref vals, .. } => vals.deform(assoc_env).map(BlockContent::from),
                parser::BlockContent::Expression(ref fe) => fe.deform(assoc_env).map(BlockContent::from)
            }).collect::<Result<_>>().map(|x| Expr::Block(p, x)),
            Lettings { ref location, ref vals, ref subexpr } => Ok(Expr::Lettings
            {
                head: location, vars: vals.deform(assoc_env)?, subexpr: box subexpr.deform(assoc_env)?
            }),
            CaseOf { ref location, ref cond, ref matchers } => Ok(Expr::CaseOf
            {
                head: location, expr: box cond.deform(assoc_env)?, matchers: matchers.deform(assoc_env)?
            })
        }
    }
}
impl<'s: 't, 't> Deformable<'s, 't> for parser::ExprPatSynTree<'s>
{
    type Deformed = ExprPat<'s, 't>;
    fn deform(&'t self, assoc_env: &AssociativityEnv<'s>) -> Result<Self::Deformed>
    {
        use parser::ExprPatSynTree::*; use self::SymPath;
        match *self
        {
            SymBinding(ref s) => Ok(ExprPat::SymBinding(GenSource::Sliced(s))),
            Numeric(ref n) => Ok(ExprPat::Numeric(n.into())),
            SymPath(ref s1, ref sv) => Ok(ExprPat::PathRef(GenSource::Sliced(s1), sv.iter().map(GenSource::Sliced).collect())),
            ArrayLiteral(ref p, ref xv) => Ok(ExprPat::ArrayLiteral(p, xv.deform(assoc_env)?)),
            Tuple(ref p, ref xv) if xv.is_empty() => Ok(ExprPat::Unit(p)),
            Tuple(_, ref xv) => Ok(ExprPat::Tuple(box xv.first().unwrap().deform(assoc_env)?, xv.deform(assoc_env)?)),
            Placeholder(ref p) => Ok(ExprPat::Placeholder(p)),
            Prefix(ref lhs, ref args) =>
            {
                let mut lhs = lhs.deform(assoc_env)?;
                lhs.apply_args(&mut args.deform(assoc_env)?).map_err(|_| DeformationError::UnableToApply(lhs.position().clone()))?;
                Ok(lhs)
            },
            Infix { ref lhs, ref mods } =>
            {
                let mut mods: Vec<_> = mods.iter().map(|&(ref op, ref rhs)| Ok(InfixIntermediate
                {
                    op, assoc: assoc_env.lookup(op.slice), ir: rhs.deform(assoc_env)?
                })).collect::<Result<_>>()?;
                let mut lhs = lhs.deform(assoc_env)?;
                while !mods.is_empty()
                {
                    let agg = extract_most_precedences(&mods).map_err(|p| DeformationError::UnresolvedAssociation(p.clone()))?.unwrap();
                    let ir = mods.remove(agg.index);
                    let cell = if agg.index >= 1 { &mut mods[agg.index - 1].ir } else { &mut lhs };
                    cell.combine_inplace(SymPath { base: ir.op.into(), desc: Vec::new() }, ir.ir);
                }
                Ok(lhs)
            }
        }
    }
}
impl<'s: 't, 't> Deformable<'s, 't> for parser::Binding<'s>
{
    type Deformed = Binding<'s, 't>;
    fn deform(&'t self, assoc_env: &AssociativityEnv<'s>) -> Result<Self::Deformed>
    {
        Ok(Binding { pat: self.pat.deform(assoc_env)?, expr: self.expr.deform(assoc_env)? })
    }
}
impl<'s: 't, 't> ExprPat<'s, 't>
{
    fn apply_args(&mut self, args: &mut Vec<Self>) -> StdResult<(), ()>
    {
        match replace(self, ExprPat::Garbage)
        {
            ExprPat::Apply(p, mut args_) => { args_.append(args); *self = ExprPat::Apply(p, args_); Ok(()) },
            ExprPat::SymBinding(s) => { *self = ExprPat::Apply(SymPath { base: s, desc: Vec::new() }, args.drain(..).collect()); Ok(()) },
            ExprPat::PathRef(sb, sv) => { *self = ExprPat::Apply(SymPath { base: sb, desc: sv }, args.drain(..).collect()); Ok(()) },
            _ => Err(())
        }
    }
    /// l self a
    fn combine(self, lhs: SymPath<'s, 't>, arg2: Self) -> Self { ExprPat::Apply(lhs, vec![self, arg2]) }
    fn combine_inplace(&mut self, lhs: SymPath<'s, 't>, arg2: Self)
    {
        let old = replace(self, ExprPat::Garbage);
        *self = old.combine(lhs, arg2);
    }
}
impl<'s: 't, 't> EqNoloc for ExprPat<'s, 't>
{
    fn eq_nolocation(&self, other: &Self) -> bool
    {
        match *self
        {
            ExprPat::Apply(ref p, ref sv) => if let ExprPat::Apply(ref p_, ref sv_) = *other
            {
                p.eq_nolocation(p_) && sv.eq_nolocation(sv_)
            }
            else { false },
            ExprPat::SymBinding(ref s) => if let ExprPat::SymBinding(ref s_) = *other { s.eq_nolocation(s_) } else { false },
            ExprPat::Numeric(ref n) => if let ExprPat::Numeric(ref n_) = *other { n.eq_nolocation(n_) } else { false },
            ExprPat::Unit(_) => if let ExprPat::Unit(_) = *other { true } else { false },
            ExprPat::Placeholder(_) => if let ExprPat::Placeholder(_) = *other { true } else { false },
            ExprPat::PathRef(ref sb, ref sv) => if let ExprPat::PathRef(ref sb_, ref sv_) = *other
            {
                sb.eq_nolocation(sb_) && sv.eq_nolocation(sv_)
            }
            else { false },
            ExprPat::Tuple(ref x0, ref xv) => if let ExprPat::Tuple(ref x0_, ref xv_) = *other
            {
                x0.eq_nolocation(x0_) && xv.eq_nolocation(xv_)
            }
            else { false },
            ExprPat::ArrayLiteral(_, ref xv) => if let ExprPat::ArrayLiteral(_, ref xv_) = *other { xv.eq_nolocation(xv_) } else { false },
            ExprPat::Garbage => false
        }
    }
}
impl<'s: 't, 't> EqNoloc for SymPath<'s, 't>
{
    fn eq_nolocation(&self, other: &Self) -> bool
    {
        self.base.eq_nolocation(&other.base) && self.desc.eq_nolocation(&other.desc)
    }
}

static NOT_TOKEN: Source<'static> = Source { pos: Location { column: 0, line: 0 }, slice: "not" };

// deformer utils //
fn ap_2options<A, F: FnOnce(A, A) -> bool>(cond: F, t: Option<A>, f: Option<A>) -> Option<bool>
{
    if t.is_none() && f.is_none() { None } else { Some(t.map_or(false, |t| f.map_or(true, |f| cond(t, f)))) }
}
fn reverse_opt_res<A, E>(opt: Option<StdResult<A, E>>) -> StdResult<Option<A>, E> { opt.map_or(Ok(None), |e| e.map(Some)) }

#[derive(Clone)]
pub struct AggPointer { prec: usize, index: usize }
fn extract_most_precedences1<'s: 't, 't, IR: 's>(mods: &[InfixIntermediate<'s, 't, IR>])
    -> StdResult<(Option<AggPointer>, Option<AggPointer>, Option<AggPointer>), &'t Location>
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
pub fn extract_most_precedences<'s: 't, 't, IR: 's>(mods: &[InfixIntermediate<'s, 't, IR>]) -> StdResult<Option<AggPointer>, &'t Location>
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

use std::io::{Result as IOResult, Write}; use PrettyPrintSink;
impl<'s: 't, 't> ::PrettyPrint for Ty<'s, 't>
{
    fn pretty_print<W: Write>(&self, dest: &mut W) -> IOResult<()>
    {
        match *self
        {
            Ty::Expressed(Prefix::Arrow(_), ref args) =>
            {
                if args.len() > 2 { dest.write(b"(")?; }
                let a0p = match args[0] { Ty::Expressed(_, ref v) => !v.is_empty(), _ => false };
                dest.print_if(b"(", a0p)?.pretty_sink(&args[0])?.print_if(b")", a0p)?;
                dest.print(b" -> ")?.pretty_sink(&args[1])?;
                if args.len() > 2 { dest.write(b")")?; }
                for a in &args[2..]
                {
                    let p = match *a { Ty::Expressed(_, ref v) => !v.is_empty(), _ => false };
                    dest.print(b" ")?.print_if(b"(", p)?.pretty_sink(a)?.print_if(b")", p)?;
                }
                Ok(())
            },
            Ty::Expressed(ref p, ref args) =>
            {
                dest.pretty_sink(p)?;
                for a in args
                {
                    let p = match *a { Ty::Expressed(_, ref v) => !v.is_empty(), _ => false };
                    dest.print(b" ")?.print_if(b"(", p)?.pretty_sink(a)?.print_if(b")", p)?;
                }
                Ok(())
            },
            Ty::Placeholder(_) => write!(dest, "_"),
            Ty::Basic(_, bt) => write!(dest, "{:?}", bt),
            Ty::Tuple(_, ref args) =>
            {
                write!(dest, "(")?;
                if let Some(a1) = args.first()
                {
                    a1.pretty_print(dest)?;
                    for a in &args[1..] { dest.print(b", ")?.pretty_sink(a)?; }
                }
                write!(dest, ")")
            },
            Ty::ArrayDim(ref base, ref index) =>
            {
                base.pretty_print(dest)?; write!(dest, "[{:?}]", index)
            },
            Ty::SafetyGarbage => unreachable!()
        }
    }
}
impl<'s: 't, 't> ::PrettyPrint for Prefix<'s, 't>
{
    fn pretty_print<W: Write>(&self, dest: &mut W) -> IOResult<()>
    {
        match *self
        {
            Prefix::Arrow(_) => dest.write(b"(->)").map(drop),
            Prefix::User(ref s) => dest.write(s.text().as_bytes()).map(drop),
            Prefix::PathRef(ref base, ref sv) =>
            {
                base.pretty_print(dest)?;
                for s in sv { write!(dest, ".{}", s.text())?; }
                Ok(())
            }
        }
    }
}

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
            assert!(c1d.eq_nolocation(&c2d), "not matching: {:?} and {:?}", c1d, c2d);
        }
        test_unify("a `Cons` b", "Cons a b");
        test_unify("(c + b) d", "(+) c b d");
        test_unify("c + d + e", "(+) ((+) c d) e");
    }
    #[test] fn expr_unification()
    {
        fn test_unify<'s>(infix: &'s str, prefix: &'s str)
        {
            let case = TokenizerState::from(infix).strip_all();
            let case2 = TokenizerState::from(prefix).strip_all();
            let c1 = ExpressionSynTree::parse(&mut PreanalyzedTokenStream::from(&case[..]), Leftmost::Nothing).expect(&format!("in case infix({})", infix));
            let c2 = ExpressionSynTree::parse(&mut PreanalyzedTokenStream::from(&case2[..]), Leftmost::Nothing).expect(&format!("in case prefix({})", prefix));
            let assoc_env = AssociativityEnv::new(None);
            let c1d = deform_expr_full(&c1, &assoc_env).expect("in deforming case infix");
            let c2d = deform_expr_full(&c2, &assoc_env).expect("in deforming case prefix");
            assert!(c1d.eq_nolocation(&c2d), "not matching: {:?} and {:?}", c1d, c2d);
        }
        test_unify("2", "2");
        test_unify("a + 3", "(+) a 3");
        test_unify("c 2 * (4 + 3)", "(*) (c 2) ((+) 4 3)");
    }
}
