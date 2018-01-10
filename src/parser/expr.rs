//! Expression Parser

use tokparse::{Location, Source, TokenKind, Keyword, TokenStream, EnclosureKind};
use super::err::*;
use parser::{ExpectingKind, Leftmost, take_current_block_begin, get_definition_leftmost, Parser};
use parser::utils::*;
use lambda::Numeric;

#[derive(Debug, Clone, PartialEq, Eq)] pub enum ExpressionSynTree<'s>
{
    SymReference(Source<'s>), Numeric(Numeric<'s>), ArrayLiteral(Location, Vec<FullExpression<'s>>),
    RefPath(Box<FullExpression<'s>>, Vec<Source<'s>>), ArrayRef(Box<FullExpression<'s>>, Box<FullExpression<'s>>),
    Prefix(Vec<FullExpression<'s>>), Infix { lhs: Box<FullExpression<'s>>, mods: Vec<(Source<'s>, FullExpression<'s>)> }, Tuple(Location, Vec<FullExpression<'s>>)
}
#[derive(Debug, Clone, PartialEq, Eq)] pub enum ExprPatSynTree<'s>
{
    SymBinding(Source<'s>), Placeholder(Location), Numeric(Numeric<'s>), ArrayLiteral(Location, Vec<ExprPatSynTree<'s>>),
    SymPath(Source<'s>, Vec<Source<'s>>), Prefix(Box<ExprPatSynTree<'s>>, Vec<ExprPatSynTree<'s>>),
    Infix { lhs: Box<ExprPatSynTree<'s>>, mods: Vec<(Source<'s>, ExprPatSynTree<'s>)> }, Tuple(Location, Vec<ExprPatSynTree<'s>>)
}
impl<'s> ExpressionSynTree<'s>
{
    pub fn position(&self) -> &Location
    {
        match *self
        {
            ExpressionSynTree::SymReference(ref s) | ExpressionSynTree::Numeric(Numeric { text: ref s, .. }) => &s.pos,
            ExpressionSynTree::ArrayLiteral(ref l, _) | ExpressionSynTree::Tuple(ref l, _) => l,
            ExpressionSynTree::RefPath(ref e, _) | ExpressionSynTree::ArrayRef(ref e, _) | ExpressionSynTree::Infix { lhs: ref e, .. } => e.position(),
            ExpressionSynTree::Prefix(ref ev) => ev.first().expect("Empty Prefix expr").position()
        }
    }
}
impl<'s> ExprPatSynTree<'s>
{
    pub fn position(&self) -> &Location
    {
        match *self
        {
            ExprPatSynTree::SymBinding(ref s) | ExprPatSynTree::Numeric(Numeric { text: ref s, .. }) | ExprPatSynTree::SymPath(ref s, _) => &s.pos,
            ExprPatSynTree::Prefix(ref x, _) | ExprPatSynTree::Infix { lhs: ref x, .. } => x.position(),
            ExprPatSynTree::ArrayLiteral(ref p, _) | ExprPatSynTree::Tuple(ref p, _) | ExprPatSynTree::Placeholder(ref p) => p
        }
    }
}

/// prefix ((op/infixident) prefix)*
fn infix_pat<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, ExprPatSynTree<'s>>
{
    let lhs = BreakParsing!(prefix_pat(stream, leftmost));
    let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(lhs.position().column)).into_exclusive();
    let mut mods = Vec::new();
    while let Ok(op) = shift_infix_ops(stream, leftmost)
    {
        let e = prefix_pat(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
        mods.place_back() <- (op.clone(), e);
    }
    Success(if mods.is_empty() { lhs } else { ExprPatSynTree::Infix { lhs: box lhs, mods } })
}
/// term term*
fn prefix_pat<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, ExprPatSynTree<'s>>
{
    let lhs = BreakParsing!(factor_pat(stream, leftmost));
    let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(lhs.position().column)).into_exclusive();
    let mut args = Vec::new();
    while let Some(a) = factor_pat(stream, leftmost).into_result_opt()? { args.push(a); }
    Success(if args.is_empty() { lhs } else { ExprPatSynTree::Prefix(box lhs, args) })
}
/// ident ("." ident)* / num / _ / "(" [infix ("," infix)*] ")"
fn factor_pat<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, ExprPatSynTree<'s>>
{
    if !leftmost.satisfy(stream.current(), true) { return NotConsumed; }
    match stream.current()
    {
        &TokenKind::Identifier(ref s) =>
        {
            stream.shift(); let mut v = Vec::new();
            while stream.shift_object_descender().is_ok()
            {
                v.place_back() <- stream.shift_identifier().map_err(|p| ParseError::Expecting(ExpectingKind::Ident, p))?.clone();
            }
            Success(if v.is_empty() { ExprPatSynTree::SymBinding(s.clone()) } else { ExprPatSynTree::SymPath(s.clone(), v) })
        },
        &TokenKind::Numeric(ref s, nty) => { stream.shift(); Success(ExprPatSynTree::Numeric(Numeric { floating: false, text: s.clone(), ty: nty })) },
        &TokenKind::NumericF(ref s, nty) => { stream.shift(); Success(ExprPatSynTree::Numeric(Numeric { floating: true, text: s.clone(), ty: nty })) },
        &TokenKind::Placeholder(ref p) => { stream.shift(); Success(ExprPatSynTree::Placeholder(p.clone())) },
        &TokenKind::BeginEnclosure(ref p, EnclosureKind::Parenthese) =>
        {
            stream.shift();
            if stream.current().is_end_enclosure_of(EnclosureKind::Parenthese)
            {
                stream.shift();
                return Success(ExprPatSynTree::Tuple(p.clone(), Vec::new()));
            }
            let mut v = vec![infix_pat(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?];
            while stream.shift_list_delimiter().is_ok()
            {
                v.place_back() <- infix_pat(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
            }
            TMatch!(stream; TokenKind::EndEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p));
            Success(if v.len() == 1 { v.pop().unwrap() } else { ExprPatSynTree::Tuple(p.clone(), v) })
        },
        _ => NotConsumed
    }
}
impl<'s> Parser<'s> for ExprPatSynTree<'s>
{
    type ResultTy = Self;
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, Self> where 's: 't { infix_pat(stream, leftmost) }
}

/// Infix <- Prefix ((op/infixident) Prefix)*
pub fn infix_expr<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>>
{
    let lhs = BreakParsing!(prefix_expr(stream, leftmost));
    let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(lhs.position().column)).into_exclusive();
    let mut rhs = Vec::new();
    while leftmost.satisfy(stream.current(), false)
    {
        match stream.current()
        {
            &TokenKind::Operator(ref s) | &TokenKind::InfixIdent(ref s) =>
            {
                let e = prefix_expr(stream.shift(), leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
                rhs.place_back() <- (s.clone(), e);
            },
            _ => break
        }
    }
    Success(if rhs.is_empty() { lhs } else { ExpressionSynTree::Infix { lhs: box lhs, mods: rhs }.into() })
}
/// Prefix <- Term Term*
pub fn prefix_expr<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>>
{
    let mut lhs = vec![BreakParsing!(term_expr(stream, leftmost))];
    let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(lhs[0].position().column)).into_exclusive();
    while let Some(rhs) = term_expr(stream, leftmost).into_result_opt()? { lhs.push(rhs); }
    Success(if lhs.len() > 1 { ExpressionSynTree::Prefix(lhs).into() } else { lhs.pop().unwrap() })
}
/// Term <- Factor (. ident / [ FullEx ])*
pub fn term_expr<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>>
{
    let mut lhs = BreakParsing!(factor_expr(stream, leftmost));
    let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(lhs.position().column)).into_exclusive();
    while leftmost.satisfy(stream.current(), false)
    {
        match stream.current()
        {
            &TokenKind::ObjectDescender(_) =>
            {
                let mut rhs = Vec::new();
                while stream.shift_object_descender().is_ok()
                {
                    rhs.place_back() <- TMatch!(stream; TokenKind::Identifier(ref s) => s.clone(), |p| ParseError::Expecting(ExpectingKind::Ident, p));
                }
                lhs = ExpressionSynTree::RefPath(box lhs.into(), rhs).into();
            },
            &TokenKind::BeginEnclosure(_, EnclosureKind::Bracket) =>
            {
                let e = FullExpression::parse(stream.shift(), leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
                if let Err(p) = stream.shift_end_enclosure_of(EnclosureKind::Bracket) { return Failed(ParseError::ExpectingClose(EnclosureKind::Bracket, p)); }
                lhs = ExpressionSynTree::ArrayRef(box lhs.into(), box e).into();
            },
            _ => break
        }
    }
    Success(lhs.into())
}
/// Factor <- ident / numeric / numericf / [ (FullEx (, FullEx)*)? ] / ( FullEx (, FullEx)* )
pub fn factor_expr<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>>
{
    if !leftmost.satisfy(stream.current(), true) { return NotConsumed; }
    match stream.current()
    {
        &TokenKind::Identifier(ref s) | &TokenKind::WrappedOp(ref s) => { stream.shift(); Success(ExpressionSynTree::SymReference(s.clone()).into()) },
        &TokenKind::Numeric (ref s, nt) => { stream.shift(); Success(ExpressionSynTree::Numeric(Numeric { floating: false, text: s.clone(), ty: nt }).into()) },
        &TokenKind::NumericF(ref s, nt) => { stream.shift(); Success(ExpressionSynTree::Numeric(Numeric { floating: true,  text: s.clone(), ty: nt }).into()) },
        &TokenKind::BeginEnclosure(ref p, EnclosureKind::Bracket) =>
        {
            stream.shift(); let leftmost = leftmost.into_exclusive();
            let es = if !stream.current().is_end_enclosure_of(EnclosureKind::Bracket)
            {
                full_expressions(stream, leftmost, Some(EnclosureKind::Bracket)).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?
            }
            else { Vec::new() };
            TMatch!(leftmost => stream; TokenKind::EndEnclosure(_, EnclosureKind::Bracket), |p| ParseError::ExpectingClose(EnclosureKind::Bracket, p));
            Success(ExpressionSynTree::ArrayLiteral(p.clone(), es).into())
        },
        &TokenKind::BeginEnclosure(ref p, EnclosureKind::Parenthese) =>
        {
            let leftmost = leftmost.into_exclusive();
            let mut e = full_expressions(stream.shift(), leftmost, Some(EnclosureKind::Parenthese))
                .into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
            TMatch!(leftmost => stream; TokenKind::EndEnclosure(_, EnclosureKind::Parenthese), |p| ParseError::ExpectingClose(EnclosureKind::Parenthese, p));
            Success(if e.len() == 1 { e.pop().unwrap() } else { ExpressionSynTree::Tuple(p.clone(), e).into() })
        },
        _ => NotConsumed
    }
}
impl<'s> Parser<'s> for ExpressionSynTree<'s>
{
    type ResultTy = FullExpression<'s>;
    /// Parses an expression
    /// # Example
    ///
    /// ```
    /// # use pureshader::*;
    /// let s = TokenizerState::from("23 + ft (vec2 4 0).x\n4").strip_all();
    /// let mut st = PreanalyzedTokenStream::from(&s[..]);
    /// ExpressionSynTree::parse(&mut st, Leftmost::Nothing).unwrap();
    /// assert!(!st.is_empty());
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>> where 's: 't { infix_expr(stream, leftmost) }
}
impl<'s> Into<FullExpression<'s>> for ExpressionSynTree<'s>
{
    fn into(self) -> FullExpression<'s> { FullExpression::Expression(self) }
}

/// Let Binding(pat = expr)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding<'s> { pub pat: ExprPatSynTree<'s>, pub expr: FullExpression<'s> }
pub type Bindings<'s> = Vec<Binding<'s>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockContent<'s>
{
    BlockVars { location: Location, vals: Bindings<'s> }, Expression(FullExpression<'s>)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FullExpression<'s>
{
    Lettings { location: Location, vals: Bindings<'s>, subexpr: Box<FullExpression<'s>> },
    Conditional { location: Location, inv: bool, cond: Box<FullExpression<'s>>, then: Box<FullExpression<'s>>, else_: Option<Box<FullExpression<'s>>> },
    CaseOf { location: Location, cond: Box<FullExpression<'s>>, matchers: Vec<(ExprPatSynTree<'s>, FullExpression<'s>)> },
    Block(Location, Vec<BlockContent<'s>>), Expression(ExpressionSynTree<'s>)
}
impl<'s> FullExpression<'s>
{
    /// source location beginning of the expression
    pub fn position(&self) -> &Location
    {
        match *self
        {
            FullExpression::Lettings { ref location, .. } | FullExpression::Conditional { ref location, .. } |
            FullExpression::Block(ref location, _) | FullExpression::CaseOf { ref location, .. } => location,
            FullExpression::Expression(ref tree) => tree.position()
        }
    }
}
impl<'s> Parser<'s> for FullExpression<'s>
{
    type ResultTy = Self;
    /// Parse a full expression(contains let, if, case-of or do)
    /// # Examples
    ///
    /// ```
    /// # use pureshader::*;
    /// let s = TokenizerState::from("let b = if true then 2 else 3 in do trace $ show b; return b").strip_all();
    /// FullExpression::parse(&mut PreanalyzedTokenStream::from(&s[..]), Leftmost::Nothing).unwrap();
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, Self> where 's: 't
    {
        if !leftmost.satisfy(stream.current(), true) { return NotConsumed; }
        match *stream.current()
        {
            TokenKind::Keyword(_, Keyword::Let) => expr_lettings(stream, leftmost),
            TokenKind::Keyword(_, Keyword::If) | TokenKind::Keyword(_, Keyword::Unless) => expr_conditional(stream, leftmost),
            TokenKind::Keyword(_, Keyword::Do) => block_content(stream),
            TokenKind::Keyword(_, Keyword::Case) => case_of(stream, leftmost),
            _ => ExpressionSynTree::parse(stream, leftmost)
        }
    }
}
pub fn full_expressions<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost, enclosure: Option<EnclosureKind>) -> ParseResult<'t, Vec<FullExpression<'s>>>
{
    let mut v = vec![BreakParsing!(FullExpression::parse(stream, leftmost))];
    let leftmost = leftmost.into_exclusive();
    while leftmost.satisfy(stream.current(), false)
    {
        match stream.current()
        {
            k if k.is_list_delimiter() =>
            {
                v.place_back() <- FullExpression::parse(stream.shift(), leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
            },
            &TokenKind::EndEnclosure(_, k) if Some(k) == enclosure => break,
            &TokenKind::EndEnclosure(ref p, k) => return Failed(ParseError::UnexpectedClose(k, p)),
            k => return Failed(ParseError::Unexpected(k.position()))
        }
    }
    Success(v)
}
/// let ... in ...
fn expr_lettings<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>>
{
    let (location, vals) = BreakParsing!(letting_common(stream, leftmost));
    let leftmost = leftmost.into_exclusive();
    TMatch!(IndentedKw; leftmost => stream; Keyword::In, ExpectingKind::LetIn);
    let subexpr = box FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
    Success(FullExpression::Lettings { location: location.clone(), vals, subexpr })
}
/// if ... then ... [else ...]
fn expr_conditional<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>>
{
    if !leftmost.satisfy(stream.current(), true) { return NotConsumed; }
    let (inv, location) = match *stream.current()
    {
        TokenKind::Keyword(ref p, Keyword::If) => { stream.shift(); (false, p) },
        TokenKind::Keyword(ref p, Keyword::Unless) => { stream.shift(); (true, p) },
        _ => return NotConsumed
    };
    let leftmost = leftmost.into_exclusive();
    let cond = box FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::ConditionExpr, stream.current().position()))?;
    TMatch!(IndentedKw; leftmost => stream; Keyword::Then);
    let then = box FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
    let else_ = if leftmost.satisfy(stream.current(), false) && stream.current().keyword() == Some(Keyword::Else)
    {
        stream.shift();
        Some(box FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?)
    }
    else { None };
    Success(FullExpression::Conditional { location: location.clone(), cond, inv, then, else_ })
}
/// do ...
fn block_content<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResult<'t, FullExpression<'s>>
{
    let location = TMatchFirst!(stream; TokenKind::Keyword(ref p, Keyword::Do) => p);
    let block_start = take_current_block_begin(stream);
    let mut s = Vec::new();
    while block_start.satisfy(stream.current(), true)
    {
        if block_start.is_explicit() && stream.current().is_end_enclosure_of(EnclosureKind::Brace) { return Success(FullExpression::Block(location.clone(), s)); }
        let defbegin = Leftmost::Inclusive(get_definition_leftmost(block_start, stream));
        if stream.current().keyword() == Some(Keyword::Let) { s.place_back() <- blk_vars(stream, defbegin)?; }
        else
        {
            match FullExpression::parse(stream, defbegin)
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
fn blk_vars<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, BlockContent<'s>>
{
    let (location, vals) = BreakParsing!(letting_common(stream, leftmost));
    let leftmost = leftmost.into_exclusive();
    if leftmost.satisfy(stream.current(), false) && stream.current().keyword() == Some(Keyword::In)
    {
        stream.shift();
        let subexpr = box FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
        Success(BlockContent::Expression(FullExpression::Lettings { location: location.clone(), vals, subexpr }))
    }
    else { Success(BlockContent::BlockVars { location: location.clone(), vals }) }
}
/// case ... of ...
fn case_of<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, FullExpression<'s>>
{
    let location = TMatchFirst!(stream; TokenKind::Keyword(ref p, Keyword::Case) => p);
    let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(location.column)).into_exclusive();
    let cond = box FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
    TMatch!(IndentedKw; leftmost => stream; Keyword::Of);
    let block_start = take_current_block_begin(stream);
    let mut matchers = Vec::new();
    while block_start.satisfy(stream.current(), true)
    {
        if block_start.is_explicit() && stream.current().is_end_enclosure_of(EnclosureKind::Brace) { break; }
        let defbegin = Leftmost::Inclusive(get_definition_leftmost(block_start, stream));
        let pat = ExprPatSynTree::parse(stream, defbegin).into_result(|| ParseError::Expecting(ExpectingKind::ExpressionPattern, stream.current().position()))?;
        let defbegin = defbegin.into_exclusive();
        TMatch!(defbegin => stream; TokenKind::TyArrow(_), |p| ParseError::Expecting(ExpectingKind::Arrow1, p));
        let xp = FullExpression::parse(stream.shift(), defbegin).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
        matchers.place_back() <- (pat, xp);
        while let TokenKind::StatementDelimiter(_) = *stream.current() { stream.shift(); }
    }
    if block_start.is_explicit() && !stream.current().is_end_enclosure_of(EnclosureKind::Brace)
    {
        return Failed(ParseError::ExpectingClose(EnclosureKind::Brace, stream.current().position()));
    }
    Success(FullExpression::CaseOf { location: location.clone(), cond, matchers })
}
/// let (bindings) [in?]
fn letting_common<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, (&'t Location, Bindings<'s>)>
{
    let location = TMatchFirst!(leftmost => stream; TokenKind::Keyword(ref p, Keyword::Let) => p);
    let block_start = take_current_block_begin(stream);
    let mut vals = Vec::new();
    while block_start.satisfy(stream.current(), true)
    {
        if stream.current().keyword() == Some(Keyword::In) { break; }
        if block_start.is_explicit() && stream.current().is_end_enclosure_of(EnclosureKind::Brace) { break; }
        let defbegin = Leftmost::Inclusive(get_definition_leftmost(block_start, stream));
        vals.place_back() <- Binding::parse(stream, defbegin).into_result(|| ParseError::Expecting(ExpectingKind::ExpressionPattern, stream.current().position()))?;
        while let TokenKind::StatementDelimiter(_) = *stream.current() { stream.shift(); }
    }
    if block_start.is_explicit() && !stream.current().is_end_enclosure_of(EnclosureKind::Brace)
    {
        return Failed(ParseError::ExpectingClose(EnclosureKind::Brace, stream.current().position()));
    }
    Success((location, vals))
}

impl<'s> Parser<'s> for Binding<'s>
{
    type ResultTy = Self;
    /// Parses a binding. `<pat> = <expr>`
    /// ## Examples
    /// ```
    /// # use pureshader::*;
    /// let s = TokenizerState::from("f (Cons x _) = x + 3").strip_all();
    /// let mut st = PreanalyzedTokenStream::from(&s[..]);
    /// Binding::parse(&mut st, Leftmost::Nothing).expect("Failed to parsing input as `Binding`");
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> ParseResult<'t, Self> where 's: 't
    {
        let pat = BreakParsing!(ExprPatSynTree::parse(stream, leftmost));
        let leftmost = leftmost.into_nothing_as(Leftmost::Exclusive(pat.position().column)).into_exclusive();
        TMatch!(leftmost => stream; TokenKind::Equal(_), |p| ParseError::Expecting(ExpectingKind::Binding, p));
        let expr = FullExpression::parse(stream, leftmost).into_result(|| ParseError::Expecting(ExpectingKind::Expression, stream.current().position()))?;
        Success(Binding { pat, expr })
    }
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
