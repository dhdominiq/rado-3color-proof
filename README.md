# Exact 3-Color Off-Diagonal Rado Numbers: R(3-AP, 3-AP, x + ay = z) = 9a + 64

A formally verified proof (in **Lean 4** + **DRAT SAT certificate**) determining the exact 3-color off-diagonal Rado number for two 3-term arithmetic progressions and the linear equation x + ay = z for all a >= 28.

## Main Theorem

Let R(a) be the smallest positive integer N such that every 3-coloring of {1, 2, ..., N} with colors {Red, Green, Blue} contains at least one of the following:
1. A monochromatic **Red** 3-term arithmetic progression (x, x+d, x+2d with d >= 1),
2. A monochromatic **Green** 3-term arithmetic progression (x, x+d, x+2d with d >= 1),
3. A monochromatic **Blue** solution to x + a*y = z (with x = y allowed).

**Theorem.** For every integer a >= 28:

    R(a) = 9a + 64

### Computed Small Values (a = 1..6)

| a | R(a) |
| :---: | :---: |
| 1 | 33 |
| 2 | 42 |
| 3 | 56 |
| 4 | 69 |
| 5 | 81 |
| 6 | 91 |

## Proof Structure & Verification

The proof is split into two machine-checked parts:

1. **Formal Reduction & Lower Bound in Lean 4 (`lean/Rado3Kolory.lean`)**
   * **Lower bound (R(a) >= 9a + 64 for all a >= 28):** Explicitly constructs a valid 3-coloring of {1, ..., 9a+63} from a 63-element 4-coloring template and proves it has zero monochromatic violations. Uses only standard Lean core axioms (`propext`, `Quot.sound`).
   * **Upper bound (R(a) <= 9a + 64 for all a >= 12):** Proves W(3,2) = 9 internally and reduces the problem to two finite facts:
     * W(3,4) = 76 (classical van der Waerden number, Beeler & O'Neil 1979),
     * K = 64: no 4-coloring of {1, ..., 64} avoids monochromatic 3-APs if {1, ..., 8} uses only colors {0, 1}.

2. **Verified SAT Certificate for K = 64 (`wyniki/K64.cnf`, `kod/08_certyfikat_K64.py`)**
   * Generated with `CaDiCaL 1.9.5` (with symmetry breaking f(1) != 1 and f(9) != 3): 256 variables, 4,434 clauses, 3,604,634 proof steps (210.84 MB DRAT file).
   * Independently verified using `drat-trim`: `s VERIFIED` (44,638,345 resolution steps in 59.3 s, log in `wyniki/09_drat_verified.txt`).

## How to Reproduce

1. Verify the Lean 4 proof (Lean 4.36.0):

    lean lean/Rado3Kolory.lean

2. Regenerate and verify the SAT proof for K = 64:

    python3 -m venv .venv && .venv/bin/pip install python-sat
    .venv/bin/python kod/08_certyfikat_K64.py

Then verify `wyniki/K64.cnf` and `wyniki/K64.drat` using `drat-trim`.

## Author

Dominik (2026), with computational & formalization assistance from AI tools.
