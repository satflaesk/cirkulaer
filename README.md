Provides a circular index type for circular indexing into primitive, fixed-size
[`array`](https://doc.rust-lang.org/std/primitive.array.html)s:

```rust
use cirkulaer::CircularIndex;

fn main() {
    const N: usize = 4;
    let mut array = [0; N];

    let mut i = CircularIndex::<N>::zero();
    array[i] = 2;
    assert_eq!(array, [2, 0, 0, 0]);

    i -= 1;
    array[i] = 5;
    assert_eq!(array, [2, 0, 0, 5]);

    i += 3;
    array[i] = 6;
    assert_eq!(array, [2, 0, 6, 5]);
}
```
