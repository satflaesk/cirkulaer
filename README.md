Provides a circular index type for circularly indexing into primitive, fixed-size
[arrays](https://doc.rust-lang.org/std/primitive.array.html):

```rust
use cirkulaer::CircularIndex;

fn main() {
    const N: usize = 5;
    let mut array = [0; N];

    let mut ci = CircularIndex::<N>::new(0).unwrap();

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
