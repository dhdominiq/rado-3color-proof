[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24476657.svg)](https://doi.org/10.5281/zenodo.24476657)

# Exact 3-Color Off-Diagonal Rado Numbers: R(3-AP, 3-AP, x + ay = z) = 9a + 64

A formally verified proof (**Lean 4** + **DRAT SAT certificate**) determining the exact 3-color off-diagonal Rado number for two 3-term arithmetic progressions and the linear equation $x + ay = z$ for all $a \ge 28$.

## Main Theorem

Let $R(a)$ be the smallest positive integer $N$ such that every 3-coloring of $\{1, 2, \dots, N\}$ with colors $\{\text{Red}, \text{Green}, \text{Blue}\}$ contains at least one of the following:
1. A monochromatic **Red** 3-term arithmetic progression ($x, x+d, x+2d$ with $d \ge 1$),
2. A monochromatic **Green** 3-term arithmetic progression ($x, x+d, x+2d$ with $d \ge 1$),
3. A monochromatic **Blue** solution to $x + ay = z$ (with $x = y$ allowed).

**Theorem.** For every integer $a \ge 28$:
$$R(a) = 9a + 64.$$

### Computed Small Values ($a = 1 \dots 6$)

| $a$ | 1 | 2 | 3 | 4 | 5 | 6 |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| $R(a)$ | 33 | 42 | 56 | 69 | 81 | 91 |

Submitted to OEIS as sequence **A400053**.

## Repository Structure

- `lean/Rado3Color.lean` — Lean 4.36.0 formalization of the explicit lower bound ($a \ge 28$) and upper-bound reduction ($a \ge 12$). Compiles without `sorry` using only standard axioms (`propext`, `Quot.sound`).
- `src/` — C++ backtracking scanners and Python SAT scripts (`CaDiCaL 1.9.5`) used to compute small values, find the restricted 4-color threshold $K = 64$, and generate the DRAT proof.
- `results/` — Experimental logs, CNF instance (`K64.cnf`), Lean verification output (`08_lean_verification.txt`), and independent `drat-trim` log (`09_drat_verification.txt`, `s VERIFIED`, 44,638,345 resolution steps).
- `paper/` — LaTeX manuscript (`main.tex`) and compiled PDF (`ramsey.pdf`).

## How to Reproduce

1. Verify the Lean 4 proof (Lean 4.36.0):

    lean lean/Rado3Color.lean

2. Regenerate and verify the SAT proof for $K = 64$:

    python3 -m venv .venv && .venv/bin/pip install python-sat
    .venv/bin/python src/08_generate_K64_drat.py

Then verify `results/K64.cnf` and `results/K64.drat` using `drat-trim`.

## Author

Dominik Pala (2026) — archived on Zenodo: [https://doi.org/10.5281/zenodo.24476657](https://doi.org/10.5281/zenodo.24476657)
