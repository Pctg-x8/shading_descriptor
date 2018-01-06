//! Temporary Data Pool

use std::vec::PlaceBack;
use std::cell::RefCell;
use std::ops::Deref;

/// Temporary Data Pool
pub struct DataPool<T>(Vec<T>);
impl<T> DataPool<T>
{
    pub fn new() -> Self { DataPool(Vec::new()) }
    pub fn create(&self, t: T) -> &T { self.0.push(t); self.latest() }
    pub fn place(&self) -> PlaceBack<T> { self.0.place_back() }
    pub fn latest(&self) -> &T { self.0.last().expect("Attempting to acquire latest item in empty pool") }
}

pub struct DataPoolReservation<'p, T: 'p, F: FnOnce() -> T>(RefCell<DataPoolReservation_<'p, T, F>>);
pub enum DataPoolReservation_<'p, T: 'p, F: FnOnce() -> T> { Reserving(&'p DataPool<T>, F), Created(&'p T) }
impl<T> DataPool<T>
{
    pub fn reserve_until_required<F: FnOnce() -> T>(&self, ctor: F) -> DataPoolReservation<T, F>
    {
        DataPoolReservation(RefCell::new(DataPoolReservation_::Reserving(self, ctor)))
    }
}
impl<'p, T: 'p, F: FnOnce() -> T> Deref for DataPoolReservation<'p, T, F>
{
    type Target = T;
    fn deref(&self) -> &T { self.acquire() }
}
impl<'p, T: 'p, F: FnOnce() -> T> DataPoolReservation<'p, T, F>
{
    pub fn acquire(&self) -> &'p T
    {
        let new_self = match *self.0.borrow()
        {
            DataPoolReservation_::Reserving(pool, ctor) =>
            {
                pool.place() <- ctor();
                DataPoolReservation_::Created(pool.latest())
            },
            r => r
        };
        *self.0.borrow_mut() = new_self; self.get()
    }
    pub fn get(&self) -> &'p T
    {
        if let DataPoolReservation_::Created(r) = *self.0.borrow() { r } else { panic!("Attempting to get a value from reserving cell") }
    }
}
