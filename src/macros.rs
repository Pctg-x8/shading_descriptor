//! Common Macros

macro_rules! CollectErrors
{
    { $e: expr =>? $collector: expr; continue } => { match $e { Err(e) => { $collector.place_back() <- e.into(); continue; }, Ok(v) => v } };
    { opt $e: expr =>? $collector: expr; continue } =>
    {
        match $e { Some(Err(e)) => { $collector.place_back() <- e.into(); continue; }, Some(Ok(v)) => Some(v), None => None }
    };
    { $e: expr =>? $collector: expr; continue $lp: tt } => { match $e { Err(e) => { $collector.place_back() <- e.into(); continue $lp; }, Ok(v) => v } };
    { $e: expr =>[?] $collector: expr; continue } => { match $e { Err(e) => { $collector.append(&mut e.into_iter().map(From::from).collect()); continue; }, Ok(v) => v } };
}
