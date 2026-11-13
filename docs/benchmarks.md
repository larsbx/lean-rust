# Initial microbenchmarks

Run `cargo bench --locked --offline --bench kernel` at each revision. The
first implementation commit is the baseline. The second commit caches the
required ambient depth at each immutable node. Scope validation becomes a
metadata check, and substitution and lifting skip subtrees whose variables
are all bound below the relevant cutoff. Construction now computes one
additional field, which these operation-only timings do not measure.

Local release run on an Intel Xeon Platinum 8573C with Rust 1.100.0.
Each workload warmed up for 1,000 iterations and reports median nanoseconds
per operation over nine batches, with the minimum and maximum batch averages.

| Workload | Baseline ns/op | Cached scope ns/op |
| --- | ---: | ---: |
| Shallow β WHNF | 97 [69–138] | 101 [61–338] |
| Closed substitution, 60 binders | 2,769 [2,650–3,198] | 21 [17–45] |
| Open substitution under a binder | 115 [98–201] | 130 [99–243] |
| Conversion through 60 β reductions | 4,188 [2,966–5,043] | 3,662 [2,503–5,652] |

The large closed-term improvement is consistent with the traversal being
skipped. The ranges overlap for the other workloads. These synthetic,
prebuilt inputs provide no throughput estimate for checking Lean libraries.
Measure expression construction and memory, mixed open-term substitution,
and conversion on representative Lean exports before further optimization.
