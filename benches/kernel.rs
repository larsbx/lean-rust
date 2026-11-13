use lean_rust_kernel::{Expr, Kernel, Kind};
use std::{hint::black_box, time::Instant};

fn node(kind: Kind) -> Expr {
    Expr::new(kind).unwrap()
}

fn sample(name: &str, rounds: u32, mut run: impl FnMut()) {
    for _ in 0..1_000 {
        run();
    }
    let mut samples = [0; 9];
    for sample in &mut samples {
        let start = Instant::now();
        for _ in 0..rounds {
            run();
        }
        *sample = start.elapsed().as_nanos() / u128::from(rounds);
    }
    samples.sort_unstable();
    println!("{name}: {} ns/op [{}–{}]", samples[4], samples[0], samples[8]);
}

fn main() {
    let ty = node(Kind::Sort(1));
    let var = node(Kind::BVar(0));
    let identity = node(Kind::Lam(ty.clone(), var.clone()));
    let shallow = node(Kind::App(identity.clone(), ty.clone()));
    let mut closed = ty.clone();
    let mut beta_chain = ty.clone();
    for _ in 0..60 {
        closed = node(Kind::Lam(ty.clone(), closed));
        beta_chain = node(Kind::App(identity.clone(), beta_chain));
    }
    let open = node(Kind::Lam(ty.clone(), node(Kind::BVar(1))));
    let kernel = Kernel::new(100_000);
    sample("shallow beta WHNF", 50_000, || {
        black_box(kernel.whnf(black_box(&shallow), 0).unwrap());
    });
    sample("closed substitution", 20_000, || {
        black_box(kernel.instantiate(black_box(&closed), &ty, 0).unwrap());
    });
    sample("open substitution", 50_000, || {
        black_box(kernel.instantiate(black_box(&open), &var, 1).unwrap());
    });
    sample("60 beta reductions", 5_000, || {
        black_box(kernel.def_eq(black_box(&beta_chain), &ty, 0).unwrap());
    });
}
