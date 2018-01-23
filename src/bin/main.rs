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
        Ok(p) => p, Err(ve) => { for e in ve { println!("Error: {}", e); } std::process::exit(1); }
    };
    if !cache.current().is_eof() { println!("Error: Compilation was not completed, remaining since {}", cache.current().position()); }
    println!("ast: {:?}", p);
    // println!("assocs: ");
    // p.dbg_print_assoc(1);
    let pd = p.deform().expect("Failed to deforming");
    println!("{:?}", pd);
    /*let ctors = ShadingPipelineConstructorEnv::new();
    p.collect_ctors(&ctors).expect("Failure in collecting type constructors");
    ctors.borrow().print_ctor_env();*/
}

/*
trait ConstructorEnvPrint
{
    fn print_ctor_env(&self);
}
impl<'s: 't, 't> ConstructorEnvPrint for ShadingPipelineConstructorEnv<'s, 't>
{
    fn print_ctor_env(&self)
    {
        if let Some(ref e) = self.vsh
        {
            println!("in Vertex Shader: ");
            e.borrow().print_ctor_env();
        }
        if let Some(ref e) = self.hsh
        {
            println!("in Hull Shader: ");
            e.borrow().print_ctor_env();
        }
        if let Some(ref e) = self.dsh
        {
            println!("in Hull Shader: ");
            e.borrow().print_ctor_env();
        }
        if let Some(ref e) = self.gsh
        {
            println!("in Hull Shader: ");
            e.borrow().print_ctor_env();
        }
        if let Some(ref e) = self.fsh
        {
            println!("in Hull Shader: ");
            e.borrow().print_ctor_env();
        }

        println!("Compilation Scope: ");
        for ty in &self.symbol_set().ty { println!("- type {}", ty.text()); }
        for &TypedDataConstructorScope { ref name, ref ty, ref ctors } in &self.symbol_set().data
        {
            std::io::stdout().print(b"- data ").unwrap()
                .print(name.text().as_bytes()).unwrap()
                .print(b"( :: ").unwrap().pretty_sink(ty).unwrap().print(b")\n").unwrap();
            for dc in ctors
            {
                std::io::stdout().print(b"-- ").unwrap()
                    .print(dc.name.text().as_bytes()).unwrap().print(b" :: ").unwrap()
                    .pretty_sink(&dc.ty).unwrap().print(b" = ").unwrap()
                    .pretty_sink(&dc.expressed).unwrap().print(b"\n").unwrap();
            }
            std::io::stdout().flush().unwrap();
        }
    }
}
impl<'s: 't, 't> ConstructorEnvPrint for ConstructorEnvPerShader<'s, 't>
{
    fn print_ctor_env(&self)
    {
        for ty in &self.symbol_set().ty { println!("- type {}", ty.text()); }
        for &TypedDataConstructorScope { ref name, ref ty, ref ctors } in &self.symbol_set().data
        {
            std::io::stdout().print(b"- data ").unwrap()
                .print(name.text().as_bytes()).unwrap()
                .print(b"( :: ").unwrap().pretty_sink(ty).unwrap().print(b")\n").unwrap();
            for dc in ctors
            {
                std::io::stdout().print(b"-- ").unwrap()
                    .print(dc.name.text().as_bytes()).unwrap().print(b" :: ").unwrap()
                    .pretty_sink(&dc.ty).unwrap().print(b" = ").unwrap()
                    .pretty_sink(&dc.expressed).unwrap().print(b"\n").unwrap();
            }
            std::io::stdout().flush().unwrap();
        }
    }
}
*/
