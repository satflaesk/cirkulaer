Provides a circular index type suitable for indexing into primitive arrays in a
circular, automatically wrapping manner:

```rust
use cirkulaer::CircularIndex;

fn main() {
    const CAPACITY: usize = 5;

    let mut array = [0; CAPACITY];
    let mut ci = CircularIndex::<CAPACITY>::new(0);

    array[ci] = 2;
    assert_eq!(array, [2, 0, 0, 0, 0]);

    ci -= 1;
    array[ci] = 4;
    assert_eq!(array, [2, 0, 0, 0, 4]);

    ci += 3;
    array[ci] = 8;

    assert_eq!(array, [2, 0, 8, 0, 4]);
}
```
