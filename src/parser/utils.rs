//! Parser utils

use tokparse::{TokenStream, TokenKind, EnclosureKind, Source, Location};

macro_rules! CheckLayout
{
	($leftmost: expr => $stream: expr) =>
	{
		if !$leftmost.satisfy($stream.current(), true) { return Err(ParseError::LayoutViolation($stream.current().position())).into(); }
	};
	($leftmost: expr => $stream: expr, NC) =>
	{
		if !$leftmost.satisfy($stream.current(), true) { return NotConsumed; }
	}
}
/// トークンマッチングマクロ
macro_rules! TMatch
{
	($leftmost: expr => $stream: expr; $pat: pat => $extract: expr, $err: expr) =>
	{{
		CheckLayout!($leftmost => $stream);
		match $stream.current().kind { $pat => { $stream.shift(); $extract }, ref e => return Err($err(e.position())) }
	}};
	($leftmost: expr => $stream: expr; $pat: pat, $err: expr) =>
	{{
		CheckLayout!($leftmost => $stream);
		match *$stream.current() { $pat => { $stream.shift(); }, ref e => return Err($err(e.position())).into() }
	}};
	($stream: expr; $pat: pat => $extract: expr, $err: expr) =>
	{
		match *$stream.current() { $pat => { $stream.shift(); $extract }, ref e => return Err($err(e.position())).into() }
	};
	(IndentedKw; $leftmost: expr => $stream: expr; $kw: expr) =>
	{
		if $leftmost.satisfy($stream.current(), true) && $stream.current().keyword() == Some($kw) { $stream.shift(); }
		else { return Failed(ParseError::Expecting(ExpectingKind::Keyword($kw), $stream.current().position())); }
	};
	(IndentedKw; $leftmost: expr => $stream: expr; $kw: expr, $expecting: expr) =>
	{
		if $leftmost.satisfy($stream.current(), true) && $stream.current().keyword() == Some($kw) { $stream.shift(); }
		else { return Failed(ParseError::Expecting($expecting, $stream.current().position())); }
	};
	($stream: expr; $pat: pat, $err: expr) =>
	{
		match *$stream.current() { $pat => { $stream.shift(); }, ref e => return Err($err(e.position())).into() }
	};
	(Numeric: $stream: expr; $err: expr) =>
	{
		match *$stream.current()
		{
			ref t@TokenKind::Numeric(_, _) | ref t@TokenKind::NumericF(_, _) => { $stream.shift(); t },
			ref e => return Err($err(e.position())).into()
		}
	};
	(Optional: $stream: expr; $pat: pat => $act: expr) =>
	{
		if let $pat = *$stream.current() { $stream.shift(); Some($act) } else { None }
	};
	(Optional: $stream: expr; $pat: pat) =>
	{
		if let $pat = *$stream.current() { $stream.shift(); true } else { false }
	}
}
/// パース頭向けマッチングマクロ(ない場合はNotConsumedを返してくれる)
macro_rules! TMatchFirst
{
	($stream: expr; $pat: pat => $extract: expr) =>
	{
		if let $pat = *$stream.current() { $stream.shift(); $extract } else { return NotConsumed; }
	};
	($stream: expr; $pat: pat) => { if let $pat = *$stream.current() { $stream.shift(); } else { return NotConsumed; } };
	($leftmost: expr => $stream: expr; $pat: pat) =>
	{
		if let $pat = *$stream.current()
		{
			if $leftmost.satisfy($stream.current(), true) { $stream.shift(); } else { return NotConsumed; }
		}
		else { return NotConsumed; }
	}
}
/// FailedまたはNotConsumedで抜ける
macro_rules! BreakParsing
{
	($e: expr) => { match $e { Success(v) => v, Failed(f) => return Failed(f), NotConsumed => return NotConsumed } };
	{ $($e: tt)* } => { match { $($e)* } { Success(v) => v, Failed(f) => return Failed(f), NotConsumed => return NotConsumed } };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Leftmost { Nothing, Inclusive(usize), Exclusive(usize) }
impl Leftmost
{
	pub fn satisfy(&self, tok: &TokenKind, always_satisfy_on_nothing: bool) -> bool
	{
		match *self
		{
			Leftmost::Inclusive(l) => l <= tok.position().column,
			Leftmost::Exclusive(l) => l < tok.position().column,
			Leftmost::Nothing => always_satisfy_on_nothing
		}
	}
	pub fn num(&self) -> Option<usize> { match *self { Leftmost::Nothing => None, Leftmost::Inclusive(n) | Leftmost::Exclusive(n) => Some(n) } }
	pub fn is_nothing(&self) -> bool { match *self { Leftmost::Nothing => true, _ => false } }
	pub fn into_exclusive(self) -> Self
	{
		match self { Leftmost::Nothing | Leftmost::Exclusive(_) => self, Leftmost::Inclusive(n) => Leftmost::Exclusive(n) }
	}
	pub fn into_nothing_as(self, nothing: Leftmost) -> Self
	{
		match self { Leftmost::Nothing => nothing, _ => self }
	}
	pub fn is_explicit(&self) -> bool { self.is_nothing() }
}

pub fn take_current_block_begin<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> Leftmost
{
	match *stream.current()
	{
		TokenKind::BeginEnclosure(_, EnclosureKind::Brace) => { stream.shift(); Leftmost::Nothing },
		TokenKind::EOF(_) => Leftmost::Inclusive(0),
		ref t => Leftmost::Inclusive(t.position().column)
	}
}
pub fn get_definition_leftmost<'s: 't, 't, S: TokenStream<'s, 't>>(block_leftmost: Leftmost, stream: &S) -> usize
{
	if stream.on_linehead() { stream.current().position().column }
	else { block_leftmost.num().unwrap_or(stream.current().position().column) }
}

// minimal/useful parsers //
pub fn take_operator<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> Result<&'t Source<'s>, &'t Location>
{
	match *stream.current() { TokenKind::Operator(ref s) => { stream.shift(); Ok(s) }, ref e => Err(e.position()) }
}
pub fn name<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost, allow_placeholder: bool) -> Result<(&'t Location, Option<&'s str>), &'t Location>
{
	if !leftmost.satisfy(stream.current(), true) { Err(stream.current().position()) }
	else
	{
		match *stream.current()
		{
			TokenKind::Placeholder(ref p) if allow_placeholder => { stream.shift(); Ok((p, None)) },
			TokenKind::Identifier(Source { slice, ref pos, .. }) => { stream.shift(); Ok((pos, Some(slice))) },
			ref e => Err(e.position())
		}
	}
}

/// op | infixindent
pub fn shift_infix_ops<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S) -> Result<&'t Source<'s>, &'t Location>
{
    match stream.current()
    {
        &TokenKind::Operator(ref s) | &TokenKind::InfixIdent(ref s) => { stream.shift(); Ok(s) },
        t => Err(t.position())
    }
}
