import os
import time
from pysat.solvers import Solver

N = 64
cnf_path = os.path.expanduser("results/K64.cnf")
drat_path = os.path.expanduser("results/K64.drat")

def var(i, c):
    return 4 * (i - 1) + c + 1

clauses = []
for i in range(1, N + 1):
    clauses.append([var(i, 0), var(i, 1), var(i, 2), var(i, 3)])
    for c1 in range(4):
        for c2 in range(c1 + 1, 4):
            clauses.append([-var(i, c1), -var(i, c2)])

# Liczby 1..8 tylko w kolorach 0 i 1
for i in range(1, 9):
    clauses.append([-var(i, 2)])
    clauses.append([-var(i, 3)])

# Proste lamanie symetrii (zamiana kolorow 0<->1 oraz 2<->3)
clauses.append([-var(1, 1)])
clauses.append([-var(9, 3)])

# Zakaz 3-AP w kazdym z 4 kolorow
for x in range(1, N + 1):
    for d in range(1, (N - x) // 2 + 1):
        for c in range(4):
            clauses.append([-var(x, c), -var(x + d, c), -var(x + 2 * d, c)])

# 1. Zapisujemy czysty plik CNF
with open(cnf_path, "w") as f:
    f.write(f"p cnf {4 * N} {len(clauses)}\n")
    for cl in clauses:
        f.write(" ".join(map(str, cl)) + " 0\n")
print(f"Zapisano zadanie: {cnf_path} ({len(clauses)} regul)", flush=True)

# 2. Szukamy najszybszego solvera, ktory potrafi wypluc certyfikat DRAT
wybrany = None
for nazwa in ("cadical195", "cadical153", "glucose42", "glucose4", "minisat22"):
    try:
        with Solver(name=nazwa, with_proof=True) as test_s:
            test_s.add_clause([1])
            test_s.add_clause([-1])
            test_s.solve()
            pr = test_s.get_proof()
            if pr is not None and len(pr) > 0:
                wybrany = nazwa
                break
    except Exception:
        continue

if not wybrany:
    print("BLAD: Zaden solver w python-sat nie obsluguje trybu with_proof.")
    raise SystemExit(1)

print(f"Generuje certyfikat DRAT za pomoca '{wybrany}' (cierpliwosci, ok. 1-2 min)...", flush=True)
t0 = time.time()
with Solver(name=wybrany, bootstrap_with=clauses, with_proof=True) as solver:
    sat = solver.solve()
    dt = time.time() - t0
    if sat:
        print("BLAD: Znaleziono kolorowanie dla N=64 (to nie powinno sie zdarzyc)!")
        raise SystemExit(1)
    proof = solver.get_proof()

with open(drat_path, "w") as f:
    for line in proof:
        f.write(line + "\n")

rozmiar_mb = os.path.getsize(drat_path) / (1024 * 1024)
print(f"GOTOWE w {dt:.2f} s!")
print(f"Zapisano certyfikat: {drat_path}")
print(f"Liczba krokow dowodu: {len(proof)} | Rozmiar: {rozmiar_mb:.2f} MB")
