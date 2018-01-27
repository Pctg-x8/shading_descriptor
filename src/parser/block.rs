//! Block related utils

use {TokenStream, Leftmost, Location, EnclosureKind};
use super::{shift_block_begin, take_current_block_begin};

/// introduces a block  
/// (`where` | `:`) [`{` ... `}`]
pub fn intro_block<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, leftmost: Leftmost) -> Result<Leftmost, &'t Location>
{
    shift_block_begin(stream, leftmost).map(|_| take_current_block_begin(stream))
}
/// try to leave from the block
pub fn outro_block<'s: 't, 't, S: TokenStream<'s, 't>>(stream: &mut S, block_leftmost: Leftmost) -> Result<(), &'t Location>
{
    if block_leftmost.is_explicit() { stream.shift_end_enclosure_of(EnclosureKind::Brace) } else { Ok(()) }
}
