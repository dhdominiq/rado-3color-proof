#include <iostream>
#include <vector>
#include <algorithm>
#include <chrono>
#include <string>

using namespace std;

struct Para {
    int u, w;
    bool operator<(const Para& other) const {
        if (u != other.u) return u < other.u;
        return w < other.w;
    }
    bool operator==(const Para& other) const {
        return u == other.u && w == other.w;
    }
};

class RadoSolver {
    int a, b, c, d, kolory;
    bool rozne;
    int N;
    vector<vector<Para>> ograniczenia;
    vector<int> kolor;

    // Przeszukiwanie z nawrotami (backtracking) + lamanie symetrii kolorow
    bool dfs(int v, int max_uzyty) {
        if (v > N) return true; // Udalo sie pokolorowac 1..N bez konfliktu

        int limit_koloru = min(max_uzyty + 1, kolory - 1);
        for (int col = 0; col <= limit_koloru; ++col) {
            kolor[v] = col;
            bool konflikt = false;

            for (const auto& p : ograniczenia[v]) {
                if (kolor[p.u] == col && kolor[p.w] == col) {
                    konflikt = true;
                    break;
                }
            }

            if (!konflikt) {
                if (dfs(v + 1, max(max_uzyty, col))) {
                    return true;
                }
            }
        }
        return false;
    }

public:
    RadoSolver(int a, int b, int c, int d, int kolory, bool rozne)
        : a(a), b(b), c(c), d(d), kolory(kolory), rozne(rozne), N(0) {}

    bool czy_da_sie(int n, vector<int>& zapisane_kolory) {
        N = n;
        ograniczenia.assign(N + 1, {});
        kolor.assign(N + 1, -1);

        // Generujemy wszystkie trojki (x, y, z) spelniajace a*x + b*y + c = d*z
        for (int x = 1; x <= N; ++x) {
            for (int y = 1; y <= N; ++y) {
                long long lewa = 1LL * a * x + 1LL * b * y + c;
                if (lewa <= 0 || lewa % d != 0) continue;
                long long z_ll = lewa / d;
                if (z_ll < 1 || z_ll > N) continue;
                int z = static_cast<int>(z_ll);

                if (rozne && (x == y || x == z || y == z)) continue;

                // Zapisujemy warunek przy najwiekszej liczbie z trojki
                int m = max({x, y, z});
                int u, w;
                if (m == x) { u = y; w = z; }
                else if (m == y) { u = x; w = z; }
                else { u = x; w = y; }

                if (u > w) swap(u, w);
                ograniczenia[m].push_back({u, w});
            }
        }

        // Usuwamy duplikaty, zeby nie sprawdzac tego samego warunku dwa razy
        for (int v = 1; v <= N; ++v) {
            sort(ograniczenia[v].begin(), ograniczenia[v].end());
            ograniczenia[v].erase(
                unique(ograniczenia[v].begin(), ograniczenia[v].end()),
                ograniczenia[v].end()
            );
        }

        if (dfs(1, -1)) {
            zapisane_kolory = kolor;
            return true;
        }
        return false;
    }
};

void testuj_rownanie(const string& nazwa, int a, int b, int c, int d, int kolory, bool rozne, int max_n = 100) {
    auto start = chrono::high_resolution_clock::now();
    RadoSolver solver(a, b, c, d, kolory, rozne);

    vector<int> najlepsze_kolorowanie;
    int wynik = -1;

    for (int n = 1; n <= max_n; ++n) {
        vector<int> aktualne;
        if (solver.czy_da_sie(n, aktualne)) {
            najlepsze_kolorowanie = aktualne;
        } else {
            wynik = n;
            break;
        }
    }

    auto koniec = chrono::high_resolution_clock::now();
    double czas_ms = chrono::duration<double, milli>(koniec - start).count();

    cout << "Rownanie: " << nazwa << " | Kolory: " << kolory
         << " | Rozne: " << (rozne ? "TAK" : "NIE") << "\n";

    if (wynik != -1) {
        cout << "  -> Liczba Rado = " << wynik << " (czas: " << czas_ms << " ms)\n";
        cout << "  -> Ostatnie dzialajace kolorowanie (dla N = " << wynik - 1 << "):\n";
        for (int c_idx = 0; c_idx < kolory; ++c_idx) {
            cout << "     Kolor " << c_idx + 1 << ": ";
            for (int i = 1; i < (int)najlepsze_kolorowanie.size(); ++i) {
                if (najlepsze_kolorowanie[i] == c_idx) cout << i << " ";
            }
            cout << "\n";
        }
    } else {
        cout << "  -> Nie znaleziono granicy do N = " << max_n << "\n";
    }
    cout << "--------------------------------------------------\n";
}

int main() {
    cout << "=== TESTY KALIBRACYJNE SOLVERA RADO ===\n\n";

    // 1. Klasyczne rownanie Schura: x + y = z
    testuj_rownanie("x + y = z", 1, 1, 0, 1, 2, false);
    testuj_rownanie("x + y = z", 1, 1, 0, 1, 3, false);

    // 2. Ciag arytmetyczny (van der Waerden): x + y = 2z (rozne liczby)
    testuj_rownanie("x + y = 2z", 1, 1, 0, 2, 2, true);
    testuj_rownanie("x + y = 2z", 1, 1, 0, 2, 3, true);

    // 3. Rownanie x + 2y = 3z (rozne liczby)
    testuj_rownanie("x + 2y = 3z", 1, 2, 0, 3, 2, true);

    return 0;
}
