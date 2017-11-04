extern crate pureshader;

use pureshader::*;
use std::io::prelude::*;

fn main()
{
    let fcontent = std::fs::File::open(std::env::args().nth(1).unwrap())
        .and_then(|mut fp| { let mut s = String::new(); fp.read_to_string(&mut s).map(move |_| s) }).unwrap();
    let stream = LayoutFreeTokenStream::from(LexemeIndentInsertions::from(Source::new(&fcontent)));
    // for t in stream { println!("{:?}", t); }

    // reconstruction
    let mut last_line = 0;
    for t in stream
    {
        if t.position().line != last_line
        {
            last_line = t.position().line;
            println!("{}", " ".repeat(t.position().column - 1));
        }
        match t
        {
            Token::Identifier(Source { slice, .. }) | Token::Operator(Source { slice, .. }) => print!("{} ", slice),
            Token::BeginEnclosure(_, ek) => match ek
            {
                EnclosureKind::Parenthese => print!("("),
                EnclosureKind::Brace => print!("{{"),
                EnclosureKind::Bracket => print!("[")
            },
            Token::EndEnclosure(_, ek) => match ek
            {
                EnclosureKind::Parenthese => print!(")"),
                EnclosureKind::Brace => print!("}}"),
                EnclosureKind::Bracket => print!("]")
            },
            Token::Placeholder(_) => print!("_"),
            Token::StatementDelimiter(_) => print!(";"),
            Token::ItemDescriptorDelimiter(_) => print!(":"),
            Token::ListDelimiter(_) => print!(","),
            Token::Keyword(_, kw) => match kw
            {
                Keyword::In => print!("in "), Keyword::Out => print!("out "), Keyword::Uniform => print!("uniform "), Keyword::Constant => print!("constant "),
                Keyword::Let => print!("let "), _ => print!("?")
            }
            _ => print!("?")
        }
    }
}
