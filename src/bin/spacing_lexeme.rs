extern crate pureshader;

use pureshader::*;
use std::io::prelude::*;

fn main()
{
    let fcontent = std::fs::File::open(std::env::args().nth(1).unwrap())
        .and_then(|mut fp| { let mut s = String::new(); fp.read_to_string(&mut s).map(move |_| s) }).unwrap();
    let stream = LexemeIndentInsertions::from(Source::new(&fcontent));
    for t in stream
    {
        println!("{:?}", t);
        if let LexemeInsertions::Token(Token::EOF(_)) = t { break; }
    }
}
