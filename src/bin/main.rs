extern crate pureshader;

use pureshader::*;
use std::cell::RefCell;
use std::io::prelude::*;

fn main()
{
    let fcontent = std::fs::File::open(std::env::args().nth(1).unwrap())
        .and_then(|mut fp| { let mut s = String::new(); fp.read_to_string(&mut s).map(move |_| s) }).unwrap();
    let src = RefCell::new(Source::new(&fcontent));
    let tvec = RefCell::new(Vec::new());
    let mut cache = TokenizerCache::new(&tvec, &src);
    while let Some(t) = cache.next()
    {
        println!("{:?}", t);
        if t == &Token::EOF { break; }
    }
}
