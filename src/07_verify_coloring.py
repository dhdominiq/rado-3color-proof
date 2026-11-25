s = "011001102033013112102203233002231332011011203202033213112123300"
assert len(s) == 63, "Zla dlugosc wzorca!"

# 1. Niezalezny test wzorca 63-znakowego (zero 3-AP w kolorach 0,1,2,3)
bledy_s = 0
for i in range(63):
    if i < 8 and s[i] not in ('0', '1'):
        bledy_s += 1
    for d in range(1, (63 - i - 1) // 2 + 1):
        if s[i] == s[i + d] == s[i + 2 * d]:
            bledy_s += 1

print(f"1. Test wzorca 63-znakowego: {'OK (0 bledow)' if bledy_s == 0 else f'BLAD ({bledy_s})'}")

# 2. Budujemy pelne 3-kolorowanie dla a = 28 (N = 9*28 + 63 = 315) i sprawdzamy WSZYSTKO recznie
a = 28
N = 9 * a + 63
kol = [''] * (N + 1)

for x in range(1, 64):
    ch = s[x - 1]
    if ch == '0': kol[x] = 'C'
    elif ch == '1': kol[x] = 'Z'
    else: kol[x] = 'N'

for x in range(64, 9 * a + 1):
    kol[x] = 'N'

for x in range(1, 64):
    ch = s[x - 1]
    if ch == '2': kol[9 * a + x] = 'C'
    elif ch == '3': kol[9 * a + x] = 'Z'
    else: kol[9 * a + x] = 'N'

bledy_cz = 0
for x in range(1, N + 1):
    if kol[x] in ('C', 'Z'):
        for d in range(1, (N - x) // 2 + 1):
            if kol[x] == kol[x + d] == kol[x + 2 * d]:
                bledy_cz += 1

bledy_n = 0
for y in range(1, N // a + 1):
    if kol[y] != 'N':
        continue
    for x in range(1, N - a * y + 1):
        if kol[x] == 'N' and kol[x + a * y] == 'N':
            bledy_n += 1

print(f"2. Test pelnego kolorowania dla a=28 (N={N}):")
print(f"   - Bledy 3-AP w C i Z: {bledy_cz}")
print(f"   - Bledy x+28y=z w N:  {bledy_n}")

# 3. Sprawdzamy, czy da sie wypchnac druga niebieska liczbe wyzej niz 11
from itertools import product
max_bez_n = 9
for m in range(10, 15):
    ok = False
    for bits in product((0, 1), repeat=m - 1): # pozycje 1..8 oraz 10..m
        arr = list(bits[:8]) + [-1] + list(bits[8:])
        bad = False
        for i in range(len(arr)):
            if arr[i] == -1: continue
            for d in range(1, (len(arr) - i - 1) // 2 + 1):
                if arr[i] == arr[i + d] == arr[i + 2 * d]:
                    bad = True
                    break
            if bad: break
        if not bad:
            ok = True
            break
    if ok:
        max_bez_n = m
    else:
        break

print(f"3. Maksymalny zasieg bez drugiej niebieskiej liczby (po 9): {max_bez_n} (wiec nastepna niebieska <= {max_bez_n + 1})")
