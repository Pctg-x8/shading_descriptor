extern crate pureshader;

use pureshader::*;
use std::io::prelude::*;

fn main()
{
    let fcontent = std::fs::File::open(std::env::args().nth(1).unwrap())
        .and_then(|mut fp| { let mut s = String::new(); fp.read_to_string(&mut s).map(move |_| s) }).unwrap();
    let toks = TokenizerState::from(Source::new(&fcontent)).strip_all();
    let mut cache = PreanalyzedTokenStream::from(&toks[..]);
    let p = match shading_pipeline(&mut cache)
    {
        Ok(p) => p, Err(ve) => { for e in ve { println!("Error: {}", e); } return; }
    };
    if !cache.current().is_eof() { println!("Error: Compilation was not completed, remaining since {}", cache.current().position()); }
    println!("ast: {:?}", p);
    println!("assocs: ");
    // p.dbg_print_assoc(1);
    /*loop
    {
        let t = cache.next();
        println!("{:?}", t);
        match t { &Token::EOF(_) | &Token::UnknownChar(_) => break, _ => () }
    }*/
}
