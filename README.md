# trestle-code

This repository contains the executable Lean code for the [`trestle`](https://github.com/FormalSAT/trestle) project.

As of October 2024, the Lean 4 compiler links *all* executable code from imported files,
even if that code is not used at the top-level by the project.
For example, typing `import Mathlib.Data.List.Defs` will include all the variants of `foldl`, `map`, etc. in compiled code.
This compilation behavior results in large binaries (e.g., ~100 MB).

This repository collects executable code for `trestle` to minimize the size of compiled binaries.
`trestle-code` is included as a sub-module in `trestle` so proofs of correctness can refer to a single version of the code
while also depending on Mathlib.

## On the split between `trestle-code` and `trestle`

The goal is for `trestle-code` to include only the executable code.
However, some theorems and definitions of the abstract model for SAT solving are necessary.