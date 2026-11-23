import time
from pysat.solvers import Solver

def var(i, c):
    return 4 * (i - 1) + c + 1

def sprawdz_4kolory(N):
    clauses = []
    for i in range(1, N + 1):
        # Kazda liczba ma dokladnie jeden z 4 kolorow (0, 1, 2, 3)
        clauses.append([var(i, 0), var(i, 1), var(i, 2), var(i, 3)])
        for c1 in range(4):
            for c2 in range(c1 + 1, 4):
                clauses.append([-var(i, c1), -var(i, c2)])

    # Liczby 1..8 moga uzywac TYLKO kolorow 0 i 1
    for i in range(1, min(8, N) + 1):
        clauses.append([-var(i, 2)])
        clauses.append([-var(i, 3)])

    # Lamanie symetrii (przyspiesza obliczenia)
    clauses.append([-var(1, 1)])
    if N >= 9:
        clauses.append([-var(9, 3)])

    # Zakaz 3-AP w kazdym z 4 kolorow
    for x in range(1, N + 1):
        for d in range(1, (N - x) // 2 + 1):
            for c in range(4):
                clauses.append([-var(x, c), -var(x + d, c), -var(x + 2 * d, c)])

    for nazwa in ("cadical195", "cadical153", "g4"):
        try:
            solver = Solver(name=nazwa, bootstrap_with=clauses)
            break
        except Exception:
            continue

    t0 = time.time()
    with solver:
        if solver.solve():
            model = set(solver.get_model())
            kol = []
            for i in range(1, N + 1):
                for c in range(4):
                    if var(i, c) in model:
                        kol.append(str(c))
                        break
            return True, time.time() - t0, "".join(kol)
        return False, time.time() - t0, None

print("=== SZUKAMY DOKLADNEJ STALEJ K (wiemy, ze K <= 76) ===", flush=True)

# Szybki test progowy (dla N=76 wiemy z twierdzenia W(3,4)=76, ze sie nie da)
lo, hi = 1, 76
ostatni_wzor = ""

for test_n in [40, 55, 65, 72, 75]:
    ok, dt, kol = sprawdz_4kolory(test_n)
    print(f"Test N={test_n:2d}: {'DA SIE' if ok else 'NIE DA SIE'} ({dt:.2f} s)", flush=True)
    if ok:
        lo = test_n
        ostatni_wzor = kol
    else:
        hi = test_n
        break

# Wyszukiwanie binarne miedzy lo i hi
while lo + 1 < hi:
    mid = (lo + hi) // 2
    ok, dt, kol = sprawdz_4kolory(mid)
    print(f"Test N={mid:2d}: {'DA SIE' if ok else 'NIE DA SIE'} ({dt:.2f} s)", flush=True)
    if ok:
        lo = mid
        ostatni_wzor = kol
    else:
        hi = mid

print(f"\n>>> WYNIK: K = {hi} <<<")
print(f"Wzór dla dużych a: R = 9*a + {hi}")
print(f"Kolorowanie dla N={hi-1}: {ostatni_wzor}")
