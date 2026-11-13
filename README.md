# lean-rust

A dependency-free Rust foundation for Lean-style expressions, capture-avoiding
single substitution, and bounded β/ζ conversion. See [the correspondence
contract](docs/kernel-correspondence.md) for the Lean rules and coverage boundary.

```sh
cargo build --locked --offline --all-targets
cargo test --locked --offline
lean --run oracle/Kernel.lean /tmp/lean-rust-cases.tsv
diff -u oracle/cases.tsv /tmp/lean-rust-cases.tsv
cargo bench --locked --offline --bench kernel
```

The Lean toolchain is pinned in `lean-toolchain`. The Rust workflow pins 1.85.0.
The Rust tests replay the checked-in oracle fixtures offline. The workflow
also regenerates the fixtures using Lean and checks for byte-for-byte agreement.
