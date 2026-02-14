use criterion::{Criterion, criterion_group, criterion_main};
use rand::prelude::*;

use cirkulaer::CircularIndex;

const N: usize = 1024;

fn add_assign(jumps: &mut [usize; N], num_add_assignments: usize) {
    let mut i = CircularIndex::<N>::zero();

    for _ in 0..num_add_assignments {
        let jump = jumps[i];
        jumps[i] = std::hint::black_box(jump);

        i += jump;
    }
}

fn benchmark_addition_assignment(c: &mut Criterion) {
    let mut rng = SmallRng::seed_from_u64(42);
    let mut jumps: [usize; N] = std::array::from_fn(|_| rng.random_range(1..N));

    let num_add_assignments = 10000 * N;

    c.bench_function("addition_assignment", |bencher| {
        bencher.iter(|| add_assign(&mut jumps, num_add_assignments))
    });
}

criterion_group!(benches, benchmark_addition_assignment);
criterion_main!(benches);
