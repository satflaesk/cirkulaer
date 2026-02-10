Provides a circular index type for circularly indexing into primitive, fixed-size
[arrays](https://doc.rust-lang.org/std/primitive.array.html):

```rust
use cirkulaer::CircularIndex;

fn main() {
    const N: usize = 5;
    let mut array = [0; N];

    let mut i = CircularIndex::<N>::zero();
    array[i] = 2;
    assert_eq!(array, [2, 0, 0, 0, 0]);

    i -= 1;
    array[i] = 4;
    assert_eq!(array, [2, 0, 0, 0, 4]);

    i += 3;
    array[i] = 8;
    assert_eq!(array, [2, 0, 8, 0, 4]);
}
```
