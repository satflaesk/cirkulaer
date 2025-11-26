#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use cirkulaer::{is_strictly_positive, Bool, CircularIndex, True};

pub struct RingBuffer<T, const CAPACITY: usize>
where
    Bool<{ is_strictly_positive(CAPACITY) }>: True,
{
    buffer: [Option<T>; CAPACITY],
    index_of_next: CircularIndex<CAPACITY>,
    index_of_oldest: CircularIndex<CAPACITY>,
}

impl<T, const CAPACITY: usize> RingBuffer<T, CAPACITY>
where
    Bool<{ is_strictly_positive(CAPACITY) }>: True,
{
    #[must_use]
    pub fn new() -> Self {
        let buffer: [Option<T>; CAPACITY] = std::array::from_fn(|_| None);

        Self {
            buffer,
            index_of_next: CircularIndex::<CAPACITY>::default(),
            index_of_oldest: CircularIndex::<CAPACITY>::default(),
        }
    }

    pub fn push(&mut self, item: T) {
        self.index_of_oldest += self.is_full() as usize;
        self.buffer[self.index_of_next] = Some(item);
        self.index_of_next += 1;
    }

    #[must_use]
    pub fn pop(&mut self) -> Option<T> {
        let oldest = self.buffer[self.index_of_oldest].take();
        self.index_of_oldest += oldest.is_some() as usize;

        oldest
    }

    #[must_use]
    fn is_full(&self) -> bool {
        (self.index_of_next == self.index_of_oldest) && self.buffer[self.index_of_oldest].is_some()
    }
}

fn main() {
    let mut rb = RingBuffer::<_, 4>::new();

    rb.push(1);
    rb.push(2);
    rb.push(3);
    rb.push(4);
    rb.push(5);
    rb.push(6);

    assert_eq!(rb.pop(), Some(3));
    assert_eq!(rb.pop(), Some(4));
    assert_eq!(rb.pop(), Some(5));
    assert_eq!(rb.pop(), Some(6));
    assert_eq!(rb.pop(), None);
}
