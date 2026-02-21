use cirkulaer::CircularIndex;

pub struct CircularBuffer<T, const CAPACITY: usize> {
    buffer: [Option<T>; CAPACITY],
    index_of_next: CircularIndex<CAPACITY>,
    index_of_oldest: CircularIndex<CAPACITY>,
}

impl<T, const CAPACITY: usize> CircularBuffer<T, CAPACITY> {
    pub fn new() -> Self {
        let buffer: [Option<T>; _] = std::array::from_fn(|_| None);
        let start_index = CircularIndex::<_>::zero();

        Self {
            buffer,
            index_of_next: start_index,
            index_of_oldest: start_index,
        }
    }

    pub fn push(&mut self, item: T) {
        if self.is_full() {
            self.index_of_oldest += 1;
        }

        self.buffer[self.index_of_next] = Some(item);
        self.index_of_next += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        let oldest = self.buffer[self.index_of_oldest].take();

        if oldest.is_some() {
            self.index_of_oldest += 1;
        }

        oldest
    }

    fn is_full(&self) -> bool {
        (self.index_of_next == self.index_of_oldest) && self.buffer[self.index_of_oldest].is_some()
    }
}

fn main() {
    let mut b = CircularBuffer::<_, 4>::new();

    b.push(1);
    b.push(2);
    b.push(3);
    b.push(4);
    b.push(5);
    b.push(6);

    assert_eq!(b.pop(), Some(3));
    assert_eq!(b.pop(), Some(4));
    assert_eq!(b.pop(), Some(5));
    assert_eq!(b.pop(), Some(6));
    assert_eq!(b.pop(), None);
}
