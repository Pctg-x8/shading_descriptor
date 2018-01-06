//! ラムダ抽象

use {NumericTy, Source, ExprDeformerIntermediate, Location};

/// 数値
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Numeric<'s: 't, 't> { pub floating: bool, pub text: &'t Source<'s>, pub ty: Option<NumericTy> }
impl<'s: 't, 't> Numeric<'s, 't> { pub fn position(&self) -> &'t ::Location { &self.text.pos } }
impl<'s: 't, 't> ::EqNoloc for Numeric<'s, 't>
{
    fn eq_nolocation(&self, other: &Self) -> bool { self.floating == other.floating && self.ty == other.ty && self.text.eq_nolocation(&other.text) }
}
/// ラムダ抽象
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lambda<'s: 't, 't>
{
    Fun { arg: &'t Source<'s>, expr: Box<Lambda<'s, 't>> },
    Apply { applier: Box<Lambda<'s, 't>>, param: Box<Lambda<'s, 't>> },
    SymRef(&'t Source<'s>), Numeric(Numeric<'s, 't>), ArrayLiteral(&'t Location, Vec<Lambda<'s, 't>>),
    DontCare, Unit(&'t Location)
}

// 組み込み関数とか(Builtin Functions)
const BF_INDEXOF: Source<'static> = ::Source { slice: "$indexof", pos: Location { column: 0, line: 0 } };
const BF_TCONS: Source<'static> = ::Source { slice: "$TCons", pos: Location { column: 0, line: 0 } };

impl<'s: 't, 't> Lambda<'s, 't>
{
    /// $indexof
    const INDEXOF: Self = Lambda::SymRef(&BF_INDEXOF);
    /// $TCons
    const TCONS: Self = Lambda::SymRef(&BF_TCONS);

    /// Deformed Expressionのラムダ抽象化
    pub fn from_expr(x: &ExprDeformerIntermediate<'s, 't>) -> Self
    {
        match *x
        {
            ExprDeformerIntermediate::Garbage => unreachable!("Accessing Garbage"),
            // a b c => (a b) c
            ExprDeformerIntermediate::Apply(ref lhs, ref args) => args.iter().map(Lambda::from_expr).fold(Lambda::SymRef(lhs), Lambda::apply),
            ExprDeformerIntermediate::Numeric(ref n) => Lambda::Numeric(n.clone()),
            ExprDeformerIntermediate::ArrayLiteral(ref p, ref xs) => Lambda::ArrayLiteral(p, xs.iter().map(Lambda::from_expr).collect()),
            ExprDeformerIntermediate::Conditional { ref cond, ref then, ref else_, .. } => Lambda::Apply
            {
                // if <cond> then <then> [else <else_>] => (<cond> <then>) <else_>
                applier: box Lambda::from_expr(cond).apply(Lambda::from_expr(then)),
                // elseがない場合はDontCare(よきにはからう)
                param: box else_.as_ref().map_or(Lambda::DontCare, |e| Lambda::from_expr(e))
            },
            // Applyの形にする: a.b.c => c (b a)
            ExprDeformerIntermediate::PathRef(ref base, ref members) =>
                members.iter().fold(Lambda::from_expr(base), |x, p| Lambda::SymRef(p).apply(x)),
            // $indexofをapply: a[2] => $indexof 2 a
            ExprDeformerIntermediate::ArrayRef(ref base, ref index) => Lambda::INDEXOF.apply(Lambda::from_expr(index)).apply(Lambda::from_expr(base)),
            // () => Unit, (a, b) => $TCons a b, (a, b, c) => $TCons ($TCons a b) c
            ExprDeformerIntermediate::Tuple1(ref x1, ref xs) =>
                xs[1..].iter().map(Lambda::from_expr).fold(Lambda::from_expr(x1), |x, xr| Lambda::TCONS.apply(x).apply(xr)),
            ExprDeformerIntermediate::Unit(p) => Lambda::Unit(p),
            _ => unimplemented!()
        }
    }

    /// combinator: application <x>
    fn apply(self, x: Self) -> Self { Lambda::Apply { applier: box self, param: box x } }
}

// ラムダ抽象にあたって
// 例えばResult t e = Ok t | Err eの場合
// Result(2 items) :: * -> * -> *, Ok :: forall t e. t -> Result t e, Err :: forall t e. e -> Result t e
// Resultは2アイテムなので、継続系のResult t eはforall r. (t -> r) -> (e -> r) -> r このとき、元の型の引数の数(この場合は2)は関係がない。
// 例) Result3 t e r = Ok t | Err eでもforall r'. (t -> r') -> (e -> r') -> r'になるし、Option a = Some a | Noneでもforall r. (a -> r) -> r -> rになる
// これを一般化すると、data T = A | B ...の時、forall r. A@/T/r/ -> B@/T/r/ -> ... -> rとなる。ここで、X@/T/r/は置換操作を表す(Xの型中のTをrに置き換え)。
// 中身: Ok t = ¥a. ¥b. a t, Err e = ¥a. ¥b. b e 渡された函数に自身の引数を適用する
// なので、Ok = ¥t. ¥a. ¥b. a t, Err = ¥e. ¥a. ¥b. b eとなる Result t e :: t -> (t -> r) -> (e -> r) -> r | e -> (t -> r) -> (e -> r) -> r

use std::collections::HashMap;
use ConstructorEnv;
use typepaint::TypedDataConstructor;

/// データコンストラクタのラムダ抽象
pub struct FnDataConstructor<'s: 't, 't>(HashMap<&'s str, HashMap<&'s str, Lambda<'s, 't>>>);

pub fn generate_datactor_matcher<'s: 't, 't>(env: &ConstructorEnv<'s, 't>) -> FnDataConstructor<'s, 't>
{
    let mut cons = HashMap::new();

    for (ref scope_ident, ref ctor_list) in &env.data
    {
        let pattern_count = ctor_list.len();
        ctor_list.iter().map(|&TypedDataConstructor(ref name, _)|)
    }

    FnDataConstructor(cons)
}
