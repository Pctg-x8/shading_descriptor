extern crate pureshader;

use pureshader::*;
use std::cell::RefCell;
use std::io::prelude::*;

fn main()
{
    let fcontent = std::fs::File::open(std::env::args().nth(1).unwrap())
        .and_then(|mut fp| { let mut s = String::new(); fp.read_to_string(&mut s).map(move |_| s) }).unwrap();
    let (src, tvec) = (RefCell::new(Source::new(&fcontent).into()), RefCell::new(Vec::new()));
    let mut cache = TokenizerCache::new(&tvec, &src);
    match shading_pipeline(&mut cache)
    {
        Ok(p) => println!("{:?}", p),
        Err(ve) => { for e in ve { println!("Error: {:?}", e); } }
    }
    /*loop
    {
        let t = cache.next();
        println!("{:?}", t);
        match t { &Token::EOF(_) | &Token::UnknownChar(_) => break, _ => () }
    }*/
}
