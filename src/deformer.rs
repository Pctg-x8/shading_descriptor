
use {Location, Source, BType, Associativity, AssociativityEnv};
use {TypeSynTree, InferredArrayDim};
use std::mem::replace;
use std::ops::Deref;
use lambda::Numeric;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenSource<'s: 't, 't> { Generated(String), Sliced(&'t Source<'s>) }
impl<'s: 't, 't> GenSource<'s, 't>
{
    pub fn text(&self) -> &str { match self { &GenSource::Generated(ref t) => t, &GenSource::Sliced(&Source { slice, .. }) => slice } }
    pub fn position(&self) -> &'t Location
    {
        match self { &GenSource::Generated(_) => &Location::EMPTY, &GenSource::Sliced(&Source { ref pos, .. }) => pos }
    }
}
impl<'s: 't, 't> EqNoloc for GenSource<'s, 't>
{
    fn eq_nolocation(&self, other: &Self) -> bool { self.text() == other.text() }
}

#[derive(Debug)] pub enum DeformationError<'t>
{
    ArgumentRequired(&'t Location), UnresolvedAssociation(&'t Location), ConstructorRequired(&'t Location),
    ApplicationProhibited(&'t Location), UnableToApply(&'t Location)
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Prefix<'s: 't, 't> { Arrow(&'t Location), User(GenSource<'s, 't>), PathRef(Box<TyDeformerIntermediate<'s, 't>>, Vec<GenSource<'s, 't>>) }
impl<'s: 't, 't> Prefix<'s, 't>
{
    pub fn position(&self) -> &'t Location
    {
        match *self
        {
            Prefix::Arrow(p) => p, Prefix::User(ref s) => s.position(), Prefix::PathRef(ref p, _) => p.position()
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
            TyDeformerIntermediate::Placeholder(p) | TyDeformerIntermediate::Tuple(p, _) | TyDeformerIntermediate::Basic(p, _) => p,
            TyDeformerIntermediate::Expressed(ref p, _) => p.position(),
            TyDeformerIntermediate::ArrayDim(ref p, _) => p.position(),
            TyDeformerIntermediate::SafetyGarbage => unreachable!("internal garbage item")
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

    /// self -> x
    pub fn arrow(self, x: Self) -> Self { TyDeformerIntermediate::Expressed(Prefix::Arrow(&Location::EMPTY), vec![self, x]) }
    /// x
    pub fn symref(x: GenSource<'s, 't>) -> Self { TyDeformerIntermediate::Expressed(Prefix::User(x), Vec::new()) }

    pub fn leftmost_symbol(&self) -> Option<&Prefix<'s, 't>>
    {
        match *self
        {
            TyDeformerIntermediate::Expressed(ref p, _) => Some(p), _ => None
        }
    }
}
impl<'s: 't, 't> EqNoloc for TyDeformerIntermediate<'s, 't>
{
    fn eq_nolocation(&self, other: &Self) -> bool
    {
        match *self
        {
            TyDeformerIntermediate::Placeholder(_) => if let TyDeformerIntermediate::Placeholder(_) = *other { true } else { false },
            TyDeformerIntermediate::Expressed(ref p, ref v) =>
                if let TyDeformerIntermediate::Expressed(ref p_, ref v_) = *other { p.eq_nolocation(p_) && v.eq_nolocation(v_) } else { false },
            TyDeformerIntermediate::SafetyGarbage => unreachable!(),
            TyDeformerIntermediate::Basic(_, bt) => if let TyDeformerIntermediate::Basic(_, bt_) = *other { bt == bt_ } else { false },
            TyDeformerIntermediate::Tuple(_, ref v) => if let TyDeformerIntermediate::Tuple(_, ref v_) = *other { v.eq_nolocation(v_) } else { false },
            TyDeformerIntermediate::ArrayDim(ref p, ref e) => if let TyDeformerIntermediate::ArrayDim(ref p_, ref e_) = *other
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
                cell.combine_inplace(Prefix::User(GenSource::Sliced(&ir.op)), ir.ir);
            }
            Ok(lhs)
        },
        // a => a, []
        TypeSynTree::SymReference(ref sym) => Ok(TyDeformerIntermediate::symref(GenSource::Sliced(sym))),
        TypeSynTree::PathRef(ref base, ref v) =>
            Ok(TyDeformerIntermediate::Expressed(Prefix::PathRef(box deform_ty(base, assoc_env)?, v.iter().map(GenSource::Sliced).collect()), Vec::new())),
        TypeSynTree::Placeholder(ref p) => Ok(TyDeformerIntermediate::Placeholder(p)),
        TypeSynTree::Basic(ref p, bt) => Ok(TyDeformerIntermediate::Basic(p, bt)),
        TypeSynTree::Tuple(ref p, ref v) => Ok(TyDeformerIntermediate::Tuple(p, v.iter().map(|t| deform_ty(t, assoc_env)).collect::<Result<_, _>>()?)),
        TypeSynTree::ArrowInfix { ref op_pos, ref lhs, ref rhs } => Ok(TyDeformerIntermediate::Expressed(Prefix::Arrow(op_pos), vec![
            deform_ty(lhs, assoc_env)?, deform_ty(rhs, assoc_env)?
        ])),
        TypeSynTree::ArrayDim { ref lhs, ref num } => Ok(TyDeformerIntermediate::ArrayDim(box deform_ty(lhs, assoc_env)?, num))
    }
}

use {ExpressionSynTree, FullExpression, BlockContent};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeformedBlockContent<'s: 't, 't>
{
    Vars(Vec<(ExprDeformerIntermediate<'s, 't>, ExprDeformerIntermediate<'s, 't>)>),
    Expr(ExprDeformerIntermediate<'s, 't>)
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprDeformerIntermediate<'s: 't, 't>
{
    Garbage,
    Apply(GenSource<'s, 't>, Vec<ExprDeformerIntermediate<'s, 't>>), Numeric(Numeric<'s, 't>),
    ArrayLiteral(&'t Location, Vec<ExprDeformerIntermediate<'s, 't>>),
    ArrayRef(Box<ExprDeformerIntermediate<'s, 't>>, Box<ExprDeformerIntermediate<'s, 't>>),
    PathRef(Box<ExprDeformerIntermediate<'s, 't>>, Vec<&'t Source<'s>>),
    Unit(&'t Location), Tuple1(Box<ExprDeformerIntermediate<'s, 't>>, Vec<ExprDeformerIntermediate<'s, 't>>),
    // full //
    Conditional
    {
        head: &'t Location, cond: Box<ExprDeformerIntermediate<'s, 't>>,
        then: Box<ExprDeformerIntermediate<'s, 't>>, else_: Option<Box<ExprDeformerIntermediate<'s, 't>>>
    },
    Block(&'t Location, Vec<DeformedBlockContent<'s, 't>>),
    Lettings { head: &'t Location, vars: Vec<(ExprDeformerIntermediate<'s, 't>, ExprDeformerIntermediate<'s, 't>)>, subexpr: Box<ExprDeformerIntermediate<'s, 't>> }
}
impl<'s: 't, 't> ExprDeformerIntermediate<'s, 't>
{
    fn assume_application(&self) -> Result<&Self, &Self>
    {
        if let ExprDeformerIntermediate::Apply(_, _) = *self { Ok(self) } else { Err(self) }
    }
    fn append_args(&mut self, args: &mut Vec<Self>)
    {
        if let ExprDeformerIntermediate::Apply(_, ref mut a) = *self { a.append(args); }
        else { unreachable!("invalid usage") }
    }
    fn combine(self, new_lhs: GenSource<'s, 't>, new_arg: Self) -> Self
    {
        ExprDeformerIntermediate::Apply(new_lhs, vec![self, new_arg])
    }
    fn combine_inplace(&mut self, new_lhs: GenSource<'s, 't>, new_arg: Self)
    {
        let old = replace(self, ExprDeformerIntermediate::Garbage);
        *self = old.combine(new_lhs, new_arg);
    }

    pub fn position(&self) -> &'t Location
    {
        match *self
        {
            ExprDeformerIntermediate::Garbage => unreachable!(),
            ExprDeformerIntermediate::Apply(ref s, _) => s.position(),
            ExprDeformerIntermediate::Numeric(ref n) => n.position(),
            ExprDeformerIntermediate::ArrayLiteral(p, _) | ExprDeformerIntermediate::Unit(p) => p,
            ExprDeformerIntermediate::ArrayRef(ref x, _) | ExprDeformerIntermediate::PathRef(ref x, _) | ExprDeformerIntermediate::Tuple1(ref x, _) => x.position(),
            ExprDeformerIntermediate::Conditional { head, .. } | ExprDeformerIntermediate::Lettings { head, .. } | ExprDeformerIntermediate::Block(head, ..) => head
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
impl<'s: 't, 't> EqNoloc for ExprDeformerIntermediate<'s, 't>
{
    fn eq_nolocation(&self, other: &Self) -> bool
    {
        match *self
        {
            ExprDeformerIntermediate::Garbage => false,
            ExprDeformerIntermediate::Apply(ref s, ref v) =>
                if let ExprDeformerIntermediate::Apply(ref s_, ref v_) = *other { s.text() == s_.text() && v.eq_nolocation(v_) } else { false },
            ExprDeformerIntermediate::Numeric(ref n) => if let ExprDeformerIntermediate::Numeric(ref n_) = *other { n.eq_nolocation(n_) } else { false },
            ExprDeformerIntermediate::ArrayLiteral(_, ref v) => if let ExprDeformerIntermediate::ArrayLiteral(_, ref v_) = *other { v.eq_nolocation(v_) } else { false },
            ExprDeformerIntermediate::Tuple1(ref x, ref v) => if let ExprDeformerIntermediate::Tuple1(ref x_, ref v_) = *other
            {
                x.eq_nolocation(x_) && v.eq_nolocation(v_)
            }
            else { false },
            ExprDeformerIntermediate::Unit(_) => if let ExprDeformerIntermediate::Unit(_) = *other { true } else { false },
            ExprDeformerIntermediate::ArrayRef(ref b, ref x) =>
                if let ExprDeformerIntermediate::ArrayRef(ref b_, ref x_) = *other { b.eq_nolocation(b_) && x.eq_nolocation(x_) } else { false },
            ExprDeformerIntermediate::PathRef(ref b, ref v) =>
                if let ExprDeformerIntermediate::PathRef(ref b_, ref v_) = *other { b.eq_nolocation(b_) && v.eq_nolocation(v_) } else { false },
            ExprDeformerIntermediate::Conditional { ref cond, ref then, ref else_, .. } =>
                if let ExprDeformerIntermediate::Conditional { cond: ref cond_, then: ref then_, else_: ref else__, .. } = *other
                {
                    cond.eq_nolocation(cond_) && then.eq_nolocation(then_) && else_.eq_nolocation(else__)
                }
                else { false },
            ExprDeformerIntermediate::Block(_, ref v) => if let ExprDeformerIntermediate::Block(_, ref v_) = *other { v.eq_nolocation(v_) } else { false },
            ExprDeformerIntermediate::Lettings { ref vars, ref subexpr, .. } =>
                if let ExprDeformerIntermediate::Lettings { vars: ref vars_, subexpr: ref subexpr_, .. } = *other
                {
                    vars.eq_nolocation(vars_) && subexpr.eq_nolocation(subexpr_)
                }
                else { false }
        }
    }
}
impl<'s: 't, 't> EqNoloc for DeformedBlockContent<'s, 't>
{
    fn eq_nolocation(&self, other: &Self) -> bool
    {
        match *self
        {
            DeformedBlockContent::Vars(ref v) => if let DeformedBlockContent::Vars(ref v_) = *other { v.eq_nolocation(v_) } else { false },
            DeformedBlockContent::Expr(ref x) => if let DeformedBlockContent::Expr(ref x_) = *other { x.eq_nolocation(x_) } else { false }
        }
    }
}
pub fn deform_expr<'s: 't, 't>(tree: &'t ExpressionSynTree<'s>, assoc_env: &AssociativityEnv<'s>) -> Result<ExprDeformerIntermediate<'s, 't>, DeformationError<'t>>
{
    match *tree
    {
        ExpressionSynTree::Prefix(ref v) =>
        {
            let mut lhs = deform_expr_full(v.first().expect("Empty PrefixExpr"), assoc_env)?;
            lhs.assume_application().map_err(|lhs| DeformationError::UnableToApply(lhs.position()))?;
            let mut args = v[1..].iter().map(|x| deform_expr_full(x, assoc_env)).collect::<Result<_, _>>()?;
            lhs.append_args(&mut args);
            Ok(lhs)
        },
        ExpressionSynTree::Infix { ref lhs, ref mods } =>
        {
            let mut mods: Vec<_> = mods.iter().map(|&(ref op, ref rhs)| Ok(InfixIntermediate
            {
                op, assoc: assoc_env.lookup(op.slice), ir: deform_expr_full(rhs, assoc_env)?
            })).collect::<Result<_, _>>()?;
            let mut lhs = deform_expr_full(lhs, assoc_env)?;
            while !mods.is_empty()
            {
                let agg = extract_most_precedences(&mods).map_err(DeformationError::UnresolvedAssociation)?.unwrap();
                let ir = mods.remove(agg.index);
                let cell = if agg.index >= 1 { &mut mods[agg.index - 1].ir } else { &mut lhs };
                cell.combine_inplace(GenSource::Sliced(&ir.op), ir.ir);
            }
            Ok(lhs)
        },
        ExpressionSynTree::SymReference(ref s) => Ok(ExprDeformerIntermediate::Apply(GenSource::Sliced(s), Vec::new())),
        ExpressionSynTree::Numeric(ref s, ty) => Ok(ExprDeformerIntermediate::Numeric(Numeric { floating: false, text: GenSource::Sliced(s), ty })),
        ExpressionSynTree::NumericF(ref s, ty) => Ok(ExprDeformerIntermediate::Numeric(Numeric { floating: true, text: GenSource::Sliced(s), ty })),
        ExpressionSynTree::ArrayLiteral(ref p, ref a) => Ok(ExprDeformerIntermediate::ArrayLiteral(p,
            a.iter().map(|x| deform_expr_full(x, assoc_env)).collect::<Result<_, _>>()?)),
        ExpressionSynTree::Tuple(ref p, ref a) => if let Some(a1) = a.first()
        {
            Ok(ExprDeformerIntermediate::Tuple1(box deform_expr_full(a1, assoc_env)?, a.iter().map(|x| deform_expr_full(x, assoc_env)).collect::<Result<_, _>>()?))
        }
        else { Ok(ExprDeformerIntermediate::Unit(p)) },
        ExpressionSynTree::ArrayRef(ref base, ref index) => Ok(ExprDeformerIntermediate::ArrayRef(
            box deform_expr_full(base, assoc_env)?, box deform_expr_full(index, assoc_env)?)),
        ExpressionSynTree::RefPath(ref base, ref path) => Ok(ExprDeformerIntermediate::PathRef(
            box deform_expr_full(base, assoc_env)?, path.iter().collect()))
    }
}
pub fn deform_expr_full<'s: 't, 't>(tree: &'t FullExpression<'s>, assoc_env: &AssociativityEnv<'s>) -> Result<ExprDeformerIntermediate<'s, 't>, DeformationError<'t>>
{
    match *tree
    {
        FullExpression::Expression(ref e) => deform_expr(e, assoc_env),
        FullExpression::Conditional { ref location, inv, ref cond, ref then, ref else_ } =>
        {
            let mut cond = deform_expr_full(cond, assoc_env)?;
            if inv { cond = ExprDeformerIntermediate::Apply(GenSource::Sliced(&NOT_TOKEN), vec![cond]); }
            let (then, else_) = (deform_expr_full(then, assoc_env)?, reverse_opt_res(else_.as_ref().map(|e| deform_expr_full(e, assoc_env)))?);
            Ok(ExprDeformerIntermediate::Conditional { head: location, cond: box cond, then: box then, else_: else_.map(Box::new) })
        },
        FullExpression::Block(ref p, ref elist) => elist.iter().map(|x| match *x
        {
            BlockContent::BlockVars { ref vals, .. } => vals.iter().map(|&(ref pat, ref x)|
                Ok((deform_expr_full(pat, assoc_env)?, deform_expr_full(x, assoc_env)?))).collect::<Result<_, _>>().map(DeformedBlockContent::Vars),
            BlockContent::Expression(ref fe) => deform_expr_full(fe, assoc_env).map(DeformedBlockContent::Expr)
        }).collect::<Result<_, _>>().map(|x| ExprDeformerIntermediate::Block(p, x)),
        FullExpression::Lettings { ref location, ref vals, ref subexpr } => Ok(ExprDeformerIntermediate::Lettings
        {
            head: location,
            vars: vals.iter().map(|&(ref p, ref x)| Ok((deform_expr_full(p, assoc_env)?, deform_expr_full(x, assoc_env)?))).collect::<Result<_, _>>()?,
            subexpr: box deform_expr_full(subexpr, assoc_env)?
        })
    }
}

static NOT_TOKEN: Source<'static> = Source { pos: Location { column: 0, line: 0 }, slice: "not" };

// deformer utils //
fn ap_2options<A, F: FnOnce(A, A) -> bool>(cond: F, t: Option<A>, f: Option<A>) -> Option<bool>
{
    if t.is_none() && f.is_none() { None } else { Some(t.map_or(false, |t| f.map_or(true, |f| cond(t, f)))) }
}
fn reverse_opt_res<A, E>(opt: Option<Result<A, E>>) -> Result<Option<A>, E> { opt.map_or(Ok(None), |e| e.map(Some)) }

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

use std::io::{Result as IOResult, Write};
impl<'s: 't, 't> TyDeformerIntermediate<'s, 't>
{
    pub fn pretty_print<W: Write>(&self, dest: &mut W) -> IOResult<()>
    {
        match *self
        {
            TyDeformerIntermediate::Expressed(Prefix::Arrow(_), ref args) =>
            {
                write!(dest, "(")?; args[0].pretty_print(dest)?; write!(dest, ") -> ")?;
                write!(dest, "(")?; args[1].pretty_print(dest)?; write!(dest, ")")?;
                for a in &args[2..] { write!(dest, " (")?; a.pretty_print(dest)?; write!(dest, ")")?; }
                Ok(())
            },
            TyDeformerIntermediate::Expressed(ref p, ref args) =>
            {
                p.pretty_print(dest)?;
                for a in args { write!(dest, " (")?; a.pretty_print(dest)?; write!(dest, ")")?; }
                Ok(())
            },
            TyDeformerIntermediate::Placeholder(_) => write!(dest, "_"),
            TyDeformerIntermediate::Basic(_, bt) => write!(dest, "{:?}", bt),
            TyDeformerIntermediate::Tuple(_, ref args) =>
            {
                write!(dest, "(")?;
                if let Some(a1) = args.first()
                {
                    a1.pretty_print(dest)?;
                    for a in &args[1..] { write!(dest, ", ")?; a.pretty_print(dest)?; }
                }
                write!(dest, ")")
            },
            TyDeformerIntermediate::ArrayDim(ref base, ref index) =>
            {
                base.pretty_print(dest)?; write!(dest, "[{:?}]", index)
            },
            TyDeformerIntermediate::SafetyGarbage => unreachable!()
        }
    }
}
impl<'s: 't, 't> Prefix<'s, 't>
{
    pub fn pretty_print<W: Write>(&self, dest: &mut W) -> IOResult<()>
    {
        match *self
        {
            Prefix::Arrow(_) => write!(dest, "(->)"),
            Prefix::User(ref s) => write!(dest, "{}", s.text()),
            Prefix::PathRef(ref base, ref sv) => { write!(dest, "(")?; base.pretty_print(dest)?; write!(dest, ")")?; for s in sv { write!(dest, ".{}", s.text())?; } Ok(()) }
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
