# Erdős Problem 809

This Lean 4 project proves the Burr–Erdős–Graham–Sós asymptotic threshold
for rainbow odd cycles. For every fixed odd cycle of length at least seven,
among graphs on `n` vertices with at least `⌊n²/4⌋ + 1` edges, the least
number of edge colors that makes every such cycle rainbow is
`n²/8 + o(n²)`.

The seven-cycle proof in `Erdos809/SevenCycle/` and the longer-cycle proof in
`Erdos809/BucicChenMa/` are assembled in `Erdos809/FinalAssembly.lean`.
`Erdos809/SevenCycle/Statement.lean` contains the exact-edge formulation used
by the seven-cycle proof; `Erdos809/Statement.lean` contains the final
graph-copy threshold.
The general maximal anti-Ramsey function and the two-clique construction live
directly under `Erdos809/`. The longer-cycle branch formalizes the
full-density result of Bucić, Chen, and Ma, [*On a maximal anti-Ramsey
conjecture of Burr, Erdős, Graham, and Sós*](https://arxiv.org/abs/2603.18952).

## Publication layout

`Challenge.lean` states the result using only Mathlib imports. Its `sorry` is
deliberate: this file is the statement to be audited, not the proof.
It defines the maximal anti-Ramsey function for any pattern graph and applies
it to Mathlib's `cycleGraph`; `SimpleGraph.Copy` includes cycles with chords.
`Erdos809/CycleCopyBridge.lean` proves this agrees with the indexed-cycle
formulation used throughout the proof.
`Solution.lean` imports the proof development and supplies the same theorem.
`comparator.json` selects `Erdos809.main_result` and the allowed axioms for
[Comparator](https://github.com/leanprover/comparator). The proof development
itself lives under `Erdos809/`.

`formalization.yaml` is a local draft. Its marked authorship, licence,
workflow, fidelity, and review fields must be completed before a registry
submission.

The Lean and Mathlib versions are fixed by `lean-toolchain`, `lakefile.toml`,
and `lake-manifest.json`.

```sh
lake update
lake build
```

The full build includes `Challenge` and therefore reports its intentional
`sorry` warning. The proof in `Solution` can also be built directly with
`lake build Solution`.
