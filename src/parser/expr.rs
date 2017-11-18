//! Expression Parser

use tokparse::{Location, Source, TokenKind, Keyword, TokenStream, NumericTy, EnclosureKind};
use super::err::*;
use parser::{ExpectingKind, Leftmost, take_current_block_begin, get_definition_leftmost};
use std::ops::Deref;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpressionFragment<'s>
{
    Identifier(Source<'s>), Numeric(Source<'s>, Option<NumericTy>), NumericF(Source<'s>, Option<NumericTy>), Operator(Source<'s>),
    Primary(Location, FullExpression<'s>), ArrayRef(Location, FullExpression<'s>), ObjectDescender(Location), ListDelimiter(Location)
}
impl<'s> ExpressionFragment<'s>
{
    pub fn text(&self) -> Option<&'s str>
    {
        match *self
        {
            ExpressionFragment::Identifier(ref s) | ExpressionFragment::Numeric(ref s, _) | ExpressionFragment::NumericF(ref s, _) | ExpressionFragment::Operator(ref s) => Some(s.slice),
            ExpressionFragment::ObjectDescender(_) => Some("."), ExpressionFragment::ListDelimiter(_) => Some(","),
            _ => None
        }
    }
    pub fn children(&self) -> Option<&FullExpression<'s>>
    {
        match *self
        {
            ExpressionFragment::Primary(_, ref x) => Some(x), _ => None
        }
    }
}
impl<'s> Into<Expression<'s>> for ExpressionFragment<'s>
{
    fn into(self) -> Expression<'s> { Expression(vec![self]) }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expression<'s>(Vec<ExpressionFragment<'s>>);
impl<'s> Deref for Expression<'s>
{
    type Target = [ExpressionFragment<'s>]; fn deref(&self) -> &[ExpressionFragment<'s>] { &self.0 }
}
impl<'s> Into<FullExpression<'s>> for Expression<'s>
{
    fn into(self) -> FullExpression<'s> { FullExpression::Expression(self) }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockContent<'s>
{
    BlockVars { location: Location, vals: Vec<(Expression<'s>, FullExpression<'s>)> },
    Expression(FullExpression<'s>)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FullExpression<'s>
{
    Lettings { location: Location, vals: Vec<(Expression<'s>, FullExpression<'s>)>, subexpr: Box<FullExpression<'s>> },
    Conditional { location: Location, inv: bool, cond: Box<FullExpression<'s>>, then: Box<FullExpression<'s>>, else_: Option<Box<FullExpression<'s>>> },
    Block(Location, Vec<BlockContent<'s>>), Expression(Expression<'s>)
}
pub fn full_expression<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize, enclosure: Option<EnclosureKind>) -> ParseResult<'t, FullExpression<'s>>
{
    match *stream.current()
    {
        TokenKind::Keyword(_, Keyword::Let) => expr_lettings(stream, leftmost),
        TokenKind::Keyword(_, Keyword::If) | TokenKind::Keyword(_, Keyword::Unless) => expr_conditional(stream, leftmost),
        TokenKind::Keyword(_, Keyword::Do) => block_content(stream),
        _ => expression(stream, leftmost, enclosure).map(Into::into)
    }
}
pub fn expr_lettings<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, FullExpression<'s>>
{
    let (location, vals) = BreakParsing!(letting_common(stream));
    TMatch!(IndentedKw; Leftmost::Exclusive(leftmost) => stream; Keyword::In, ExpectingKind::LetIn);
    let subexpr = box full_expression(stream, leftmost, None).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
    Success(FullExpression::Lettings { location: location.clone(), vals, subexpr })
}
pub fn expr_conditional<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, FullExpression<'s>>
{
    let (inv, location) = match *stream.current()
    {
        TokenKind::Keyword(ref p, Keyword::If) => { stream.shift(); (false, p) },
        TokenKind::Keyword(ref p, Keyword::Unless) => { stream.shift(); (true, p) },
        _ => return NotConsumed
    };
    let cond = box full_expression(stream, leftmost, None).into_result(|| ParseError::Expecting(ExpectingKind::ConditionExpr, stream.current().position()))?;
    TMatch!(IndentedKw; Leftmost::Exclusive(leftmost) => stream; Keyword::Then);
    let then = box full_expression(stream, leftmost, None).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
    let else_ = if Leftmost::Exclusive(leftmost).satisfy(stream.current(), false) && stream.current().keyword() == Some(Keyword::Else)
    {
        stream.shift();
        Some(box full_expression(stream, leftmost, None).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?)
    }
    else { None };
    Success(FullExpression::Conditional { location: location.clone(), cond, inv, then, else_ })
}
pub fn block_content<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResult<'t, FullExpression<'s>>
{
    let location = TMatchFirst!(stream; TokenKind::Keyword(ref p, Keyword::Do) => p);
    let block_start = take_current_block_begin(stream);
    let mut s = Vec::new();
    while block_start.satisfy(stream.current(), true)
    {
        if block_start.is_explicit() && stream.current().is_end_enclosure_of(EnclosureKind::Brace) { return Success(FullExpression::Block(location.clone(), s)); }
        let defbegin = get_definition_leftmost(block_start, stream);
        if stream.current().keyword() == Some(Keyword::Let) { s.place_back() <- blk_vars(stream, defbegin)?; }
        else
        {
            match full_expression(stream, defbegin, None)
            {
                Success(x) => { s.place_back() <- BlockContent::Expression(x); },
                Failed(f) => return Failed(f),
                NotConsumed => break
            }
        }
    }
    if block_start.is_explicit() && !stream.current().is_end_enclosure_of(EnclosureKind::Brace) { return Failed(ParseError::ExpectingClose(EnclosureKind::Brace, stream.current().position())); }
    Success(FullExpression::Block(location.clone(), s))
}
pub fn blk_vars<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize) -> ParseResult<'t, BlockContent<'s>>
{
    let (location, vals) = BreakParsing!(letting_common(stream));
    if Leftmost::Exclusive(leftmost).satisfy(stream.current(), false) && stream.current().keyword() == Some(Keyword::In)
    {
        stream.shift();
        let subexpr = box full_expression(stream, leftmost, None).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
        Success(BlockContent::Expression(FullExpression::Lettings { location: location.clone(), vals, subexpr }))
    }
    else { Success(BlockContent::BlockVars { location: location.clone(), vals }) }
}
pub fn letting_common<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResult<'t, (&'t Location, Vec<(Expression<'s>, FullExpression<'s>)>)>
{
    // let 〜(decls) [in?]
    let location = TMatchFirst!(stream; TokenKind::Keyword(ref p, Keyword::Let) => p);
    let block_start = take_current_block_begin(stream);
    let mut vals = Vec::new();
    while block_start.satisfy(stream.current(), true)
    {
        if stream.current().keyword() == Some(Keyword::In) { break; }
        if block_start.is_explicit() && stream.current().is_end_enclosure_of(EnclosureKind::Brace) { break; }
        let defbegin = get_definition_leftmost(block_start, stream);
        let pat = expression(stream, defbegin, None).into_result(|| ParseError::Expecting(ExpectingKind::ExpressionPattern, stream.current().position()))?;
        if !stream.current().is_equal() || !Leftmost::Exclusive(defbegin).satisfy(stream.current(), false)
        {
            return Failed(ParseError::Expecting(ExpectingKind::ConcreteExpression, stream.current().position()));
        }
        stream.shift(); CheckLayout!(Leftmost::Exclusive(defbegin) => stream);
        let rhs = full_expression(stream, defbegin, None).into_result(|| ParseError::Expecting(ExpectingKind::ConcreteExpression, stream.current().position()))?;
        vals.place_back() <- (pat, rhs);
        while TMatch!(Optional: stream; TokenKind::StatementDelimiter(_)) {  }
    }
    if block_start.is_explicit() && !stream.current().is_end_enclosure_of(EnclosureKind::Brace) { return Failed(ParseError::ExpectingClose(EnclosureKind::Brace, stream.current().position())); }
    Success((location, vals))
}

/// Parses an expression
/// # Example
///
/// ```
/// # use pureshader::*;
/// # use std::cell::RefCell;
/// let (s, v) = (RefCell::new(Source::new("23 + ft (vec2 4 0).x\n4").into()), RefCell::new(Vec::new()));
/// let mut tokcache = TokenizerCache::new(&v, &s);
/// let expr = expression(&mut tokcache, 1, None).into_result_opt().unwrap().unwrap();
/// assert_eq!(expr[0].text(), Some("23"));
/// assert_eq!(expr[1].text(), Some("+"));
/// assert_eq!(expr[2].text(), Some("ft"));
/// if let &FullExpression::Expression(ref e) = expr[3].children().unwrap()
/// {
///   assert_eq!(e[0].text(), Some("vec2"));
///   assert_eq!(e[1].text(), Some("4"));
///   assert_eq!(e[2].text(), Some("0"));
/// }
/// else { unreachable!() }
/// assert_eq!(expr[4], ExpressionFragment::ObjectDescender(Location { line: 1, column: 19 }));
/// assert_eq!(expr[5].text(), Some("x"));
/// assert_eq!(tokcache.current(), &TokenKind::Numeric(Source { pos: Location { line: 2, column: 1 }, slice: "4" }, None));
/// ```
pub fn expression<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: usize, corresponding_closing: Option<EnclosureKind>) -> ParseResult<'t, Expression<'s>>
{
    #[derive(Debug)]
    enum ConvResult<'s: 't, 't> { Fragment(ExpressionFragment<'s>), Enter(&'t Location, EnclosureKind), Leave, Term, Failed(ParseError<'t>) }
    fn conv_fragment<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, corresponding_closing: Option<EnclosureKind>) -> ConvResult<'s, 't>
    {
        match *stream.current()
        {
            TokenKind::EOF(ref p) => if let Some(k) = corresponding_closing { ConvResult::Failed(ParseError::ExpectingClose(k, p)) } else { ConvResult::Term },
            TokenKind::BeginEnclosure(ref p, k@EnclosureKind::Parenthese) | TokenKind::BeginEnclosure(ref p, k@EnclosureKind::Bracket) => { stream.shift(); ConvResult::Enter(p, k) },
            TokenKind::EndEnclosure(_, k) if Some(k) == corresponding_closing => { stream.shift(); ConvResult::Leave },
            TokenKind::Identifier(ref s)  => { stream.shift(); ConvResult::Fragment(ExpressionFragment::Identifier(s.clone())) },
            TokenKind::Numeric(ref s, t)  => { stream.shift(); ConvResult::Fragment(ExpressionFragment::Numeric(s.clone(), t)) },
            TokenKind::NumericF(ref s, t) => { stream.shift(); ConvResult::Fragment(ExpressionFragment::NumericF(s.clone(), t)) },
            TokenKind::Operator(ref s)    => { stream.shift(); ConvResult::Fragment(ExpressionFragment::Operator(s.clone())) },
            TokenKind::ObjectDescender(ref p) => { stream.shift(); ConvResult::Fragment(ExpressionFragment::ObjectDescender(p.clone())) },
            TokenKind::ListDelimiter(ref p)   => { stream.shift(); ConvResult::Fragment(ExpressionFragment::ListDelimiter(p.clone())) },
            TokenKind::EndEnclosure(ref p, k) => ConvResult::Failed(ParseError::UnexpectedClose(k, p)),
            _ => ConvResult::Term
        }
    }
    let mut v = Vec::new();
    match conv_fragment(stream, corresponding_closing)
    {
        ConvResult::Fragment(f) => v.push(f),
        ConvResult::Enter(p, EnclosureKind::Parenthese) => { v.place_back() <- ExpressionFragment::Primary(p.clone(), full_expression(stream, leftmost, Some(EnclosureKind::Parenthese))?); },
        ConvResult::Enter(p, EnclosureKind::Bracket) => { v.place_back() <- ExpressionFragment::ArrayRef(p.clone(), full_expression(stream, leftmost, Some(EnclosureKind::Bracket))?); },
        ConvResult::Enter(_, _) => unreachable!(),
        ConvResult::Leave => return Success(Expression(v)),
        ConvResult::Term => return NotConsumed,
        ConvResult::Failed(f) => return Failed(f)
    }
    while Leftmost::Exclusive(leftmost).satisfy(stream.current(), false)
    {
        match conv_fragment(stream, corresponding_closing)
        {
            ConvResult::Fragment(f) => v.push(f),
            ConvResult::Enter(p, EnclosureKind::Parenthese) => { v.place_back() <- ExpressionFragment::Primary(p.clone(), full_expression(stream, leftmost, Some(EnclosureKind::Parenthese))?); },
            ConvResult::Enter(p, EnclosureKind::Bracket) => { v.place_back() <- ExpressionFragment::ArrayRef(p.clone(), full_expression(stream, leftmost, Some(EnclosureKind::Bracket))?); },
            ConvResult::Enter(_, _) => unreachable!(),
            ConvResult::Leave | ConvResult::Term => break,
            ConvResult::Failed(f) => return Failed(f)
        }
    }
    Success(Expression(v))
}

/*
/// ラムダ抽象
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lambda<'s> { Binder(&'s str, Box<Lambda<'s>>), Expression(Expression<'s>) }
// let a b = \x -> c ==> let a = \b -> \x -> c (bを移項する)
// let a ~> b = a / b ==> let (~>) a b = a / b ==> let ~> = \a -> \b -> a / b (二項演算パターンを分解してa, bを右から移項する)
// let (n ~> m) x = ... ==> let n ~> m = \x -> ... ==> let ~> = \n -> \m -> \x -> ... (関数適用パターンとみて先に移項する)
// let f (Ty a) = ... ==> let f a0 | Ty a = a0 = ... ==> let f a0 = case a0 of Ty a => ... ==> let f = \a0 -> case a0 of Ty a => ...
//  (コンストラクタパターンをa0(自動生成)に置換してガード化、その後caseに置換して最後にa0を移項)

// f a ([Var "f", Var "a"]) => 最後の1ブロックになるまで移項 => "f" = Lambda::Binder (Var "a") ...
// a ~> b ([Op "~>" (Var "a") (Var "b")]) => もともと(~>) a bの形になっているのでそのまま最後の1ブロックになるまで移項 => "~>" = Lambda::Binder (Var "a") (Lambda::Binder (Var "b") ...)
// data f4 = f4 float float float float, f4 x y z w = \c -> c x y z w
// case v of f4 x y z w => x + y + z + w => v (\x -> \y -> \z -> \w -> x + y + z + w)
//   => (\c -> c x y z w) (\x -> \y -> \z -> \w -> x + y + z + w)
// data Either a b = Left a | Right b, Left a = \l -> \r -> l a, Right b = \l -> \r -> r b
// case x of Left a => a + 3 ==> x (\a -> a + 3) (\_ -> <<Error(どうしよう)>>)
*/
