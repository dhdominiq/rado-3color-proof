import time
from pysat.solvers import Solver

def var(i, c):
    return 3 * (i - 1) + c + 1

def sprawdz_sat(N, a):
    clauses = []
    for i in range(1, N + 1):
        # Kazda liczba ma dokladnie jeden z 3 kolorow (0=C, 1=Z, 2=N)
        clauses.append([var(i, 0), var(i, 1), var(i, 2)])
        clauses.append([-var(i, 0), -var(i, 1)])
        clauses.append([-var(i, 0), -var(i, 2)])
        clauses.append([-var(i, 1), -var(i, 2)])

    # Kolory 0 i 1 maja te same zasady, wiec liczba 1 nie musi miec koloru 1
    clauses.append([-var(1, 1)])

    # Kolor 0 (C) i Kolor 1 (Z): zakaz 3 liczb w rownych odstepach
    for x in range(1, N + 1):
        for d in range(1, (N - x) // 2 + 1):
            z = x + d
            y = x + 2 * d
            clauses.append([-var(x, 0), -var(z, 0), -var(y, 0)])
            clauses.append([-var(x, 1), -var(z, 1), -var(y, 1)])

    # Kolor 2 (N): zakaz x + a*y = z (powtorzenia dozwolone)
    for y in range(1, N // a + 1):
        for x in range(1, N - a * y + 1):
            z = x + a * y
            clauses.append(list({-var(x, 2), -var(y, 2), -var(z, 2)}))

    for nazwa in ("cadical195", "cadical153", "g4"):
        try:
            solver = Solver(name=nazwa, bootstrap_with=clauses)
            break
        except Exception:
            continue

    with solver:
        if solver.solve():
            model = set(solver.get_model())
            kolory = []
            for i in range(1, N + 1):
                if var(i, 0) in model: kolory.append('C')
                elif var(i, 1) in model: kolory.append('Z')
                else: kolory.append('N')
            return True, "".join(kolory)
        return False, None

def znajdz_rado(a, start_hi=40):
    t0 = time.time()
    lo = 1
    hi = start_hi
    ostatnie = ""

    # Szukamy gornej granicy, gdzie juz sie nie da
    while True:
        ok, kol = sprawdz_sat(hi, a)
        if ok:
            lo = hi
            ostatnie = kol
            hi *= 2
        else:
            break

    # Wyszukiwanie binarne dokladnej granicy
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        ok, kol = sprawdz_sat(mid, a)
        if ok:
            lo = mid
            ostatnie = kol
        else:
            hi = mid

    czas = time.time() - t0
    return hi, czas, ostatnie

print("=== SOLVER SAT (3 kolory): 3-AP vs 3-AP vs (x + a*y = z) ===", flush=True)
prev = None
for a in range(1, 7):
    start_hi = (prev + 15) if prev else 35
    R, czas, kol = znajdz_rado(a, start_hi=start_hi)
    skok = f"(+{R - prev:2d})" if prev is not None else "     "
    print(f"a={a} | R = {R:3d} {skok} | {czas:5.2f} s | {kol}", flush=True)
    prev = R
