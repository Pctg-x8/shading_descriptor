//! Temporary Data Pool

use std::vec::PlaceBack;

/// Temporary Data Pool
/// ## Usage
///
/// ```
/// # use pureshader::DataPool;
///
/// let p = DataPool::new();
/// assert_eq!(p.create(2), 2);
/// assert_eq!(p.latest(), 2);
/// p.place() <- 3;
/// assert_eq!(p.latest(), 3);
/// ```
pub struct DataPool<T>(Vec<T>);
impl<T> DataPool<T>
{
    pub fn new() -> Self { DataPool(Vec::new()) }
    pub fn create(&mut self, t: T) -> &T { self.0.push(t); self.latest() }
    pub fn place(&mut self) -> PlaceBack<T> { self.0.place_back() }
    pub fn latest(&self) -> &T { self.0.last().expect("Attempting to acquire latest item in empty pool") }
}
