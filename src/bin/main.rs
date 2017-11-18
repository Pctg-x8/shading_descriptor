extern crate pureshader;

use pureshader::*;
use std::io::prelude::*;

fn main()
{
    let fcontent = std::fs::File::open(std::env::args().nth(1).unwrap())
        .and_then(|mut fp| { let mut s = String::new(); fp.read_to_string(&mut s).map(move |_| s) }).unwrap();
    let toks = TokenizerState::from(Source::new(&fcontent)).all();
    let mut cache = PreanalyzedTokenStream::from(&toks[..]);
    match shading_pipeline(&mut cache)
    {
        Ok(p) => println!("{:?}", p),
        Err(ve) => { for e in ve { println!("Error: {}", e); } }
    }
    if !cache.current().is_eof() { println!("Error: Compilation was not completed, remaining since {}", cache.current().position()); }
    /*loop
    {
        let t = cache.next();
        println!("{:?}", t);
        match t { &Token::EOF(_) | &Token::UnknownChar(_) => break, _ => () }
    }*/
}
