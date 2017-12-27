//! Parsing with Associativity

use super::err::*;
use std::collections::HashMap;
use std::rc::{Rc, Weak};
use std::cell::RefCell;
use tokparse::{TokenStream, TokenKind, Keyword, Source, Location};
use RcMut;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Associativity { Left(usize), Right(usize), None(usize) }
impl Default for Associativity { fn default() -> Self { Associativity::Left(9) } }
#[derive(Debug, Clone)]
pub struct AssociativityEnv<'s>
{
    pub ops: HashMap<&'s str, (Location, Associativity)>, pub parent: Option<Weak<RefCell<AssociativityEnv<'s>>>>
}
impl<'s> AssociativityEnv<'s>
{
    pub fn new(parent: Option<&Rc<RefCell<AssociativityEnv<'s>>>>) -> Self
    {
        AssociativityEnv { ops: HashMap::new(), parent: parent.map(Rc::downgrade) }
    }
    pub fn register(&mut self, op: &'s str, pos: Location, assoc: Associativity) -> Option<&Location>
    {
        match self.ops.entry(op)
        {
            ::std::collections::hash_map::Entry::Occupied(e) => Some(&e.into_mut().0),
            v => { v.or_insert((pos, assoc)); None }
        }
    }
    pub fn lookup(&self, op: &'s str) -> Associativity
    {
        self.ops.get(op).map(|&(_, ref a)| a.clone()).or_else(|| self.parent.as_ref().and_then(Weak::upgrade).map(|x| x.borrow().lookup(op)))
            .unwrap_or_default()
    }
}
pub trait AssociativityEnvironment<'s> { fn assoc_env(&self) -> &RcMut<AssociativityEnv<'s>>; }

impl<'s> super::FreeParser<'s> for Associativity
{
    type ResultTy = (Vec<Source<'s>>, Associativity);
    /// Parses an associativity declaration
    /// ## Examples
    /// ```
    /// # use pureshader::*;
    /// let s = TokenizerState::from("infixl 3 +").strip_all();
    /// let (ops, assoc) = Associativity::parse(&mut PreanalyzedTokenStream::from(&s[..])).unwrap();
    /// assert_eq!(ops, vec![Source { slice: "+", pos: Location { line: 1, column: 10 } }]);
    /// assert_eq!(assoc, Associativity::Left(3));
    /// ```
    fn parse<'t, S: TokenStream<'s, 't>>(stream: &mut S) -> ParseResult<'t, Self::ResultTy> where 's: 't
    {
        let assoc = match *stream.current()
        {
            TokenKind::Keyword(_, Keyword::Infix) =>
            {
                stream.shift();
                Associativity::None(TMatch!(Numeric: stream; |p| ParseError::Expecting(ExpectingKind::AssocPriority, p)).as_usize())
            },
            TokenKind::Keyword(_, Keyword::Infixl) =>
            {
                stream.shift();
                Associativity::Left(TMatch!(Numeric: stream; |p| ParseError::Expecting(ExpectingKind::AssocPriority, p)).as_usize())
            },
            TokenKind::Keyword(_, Keyword::Infixr) =>
            {
                stream.shift();
                Associativity::Right(TMatch!(Numeric: stream; |p| ParseError::Expecting(ExpectingKind::AssocPriority, p)).as_usize())
            },
            _ => return NotConsumed
        };
        let mut ops = vec![TMatch!(stream; TokenKind::Operator(ref s) => s.clone(), |p| ParseError::Expecting(ExpectingKind::Operator, p))];
        while stream.current().is_list_delimiter()
        {
            stream.shift();
            ops.place_back() <- TMatch!(stream; TokenKind::Operator(ref s) => s.clone(), |p| ParseError::Expecting(ExpectingKind::Operator, p));
        }
        Success((ops, assoc))
    }
}
