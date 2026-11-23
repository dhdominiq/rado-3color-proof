#include <iostream>
#include <vector>
#include <algorithm>
#include <chrono>
#include <string>
#include <iomanip>

using namespace std;

struct Rownanie {
    int a, b, c, d;
    bool rozne;
};

struct Para {
    int u, w;
    bool operator<(const Para& o) const { return u != o.u ? u < o.u : w < o.w; }
    bool operator==(const Para& o) const { return u == o.u && w == o.w; }
};

enum class Status { DA_SIE, NIE_DA_SIE, TIMEOUT };

class MultiRadoSolver {
    vector<Rownanie> eqs;
    int kolory, N;
    vector<vector<vector<Para>>> ogr;
    vector<int> kolor;
    long long wezly;
    bool timeout;
    chrono::steady_clock::time_point deadline;

    bool dfs(int v) {
        if (timeout) return false;
        if ((++wezly & 4095) == 0 && chrono::steady_clock::now() > deadline) {
            timeout = true;
            return false;
        }
        if (v > N) return true;
        for (int col = 0; col < kolory; ++col) {
            kolor[v] = col;
            bool konflikt = false;
            for (const auto& p : ogr[col][v]) {
                if (kolor[p.u] == col && kolor[p.w] == col) { konflikt = true; break; }
            }
            if (!konflikt && dfs(v + 1)) return true;
        }
        return false;
    }

public:
    MultiRadoSolver(const vector<Rownanie>& eqs) : eqs(eqs), kolory((int)eqs.size()), N(0), wezly(0), timeout(false) {}

    Status sprawdz(int n, int limit_ms) {
        N = n;
        ogr.assign(kolory, vector<vector<Para>>(N + 1));
        kolor.assign(N + 1, -1);
        wezly = 0;
        timeout = false;
        deadline = chrono::steady_clock::now() + chrono::milliseconds(limit_ms);

        for (int col = 0; col < kolory; ++col) {
            const auto& e = eqs[col];
            for (int x = 1; x <= N; ++x) {
                for (int y = 1; y <= N; ++y) {
                    long long lewa = 1LL * e.a * x + 1LL * e.b * y + e.c;
                    if (lewa <= 0 || lewa % e.d != 0) continue;
                    long long z_ll = lewa / e.d;
                    if (z_ll < 1 || z_ll > N) continue;
                    int z = (int)z_ll;
                    if (e.rozne && (x == y || x == z || y == z)) continue;

                    int m = max(x, max(y, z));
                    int u = (m == x) ? y : x;
                    int w = (m == z) ? y : z;
                    if (u > w) swap(u, w);
                    ogr[col][m].push_back({u, w});
                }
            }
            for (int v = 1; v <= N; ++v) {
                sort(ogr[col][v].begin(), ogr[col][v].end());
                ogr[col][v].erase(unique(ogr[col][v].begin(), ogr[col][v].end()), ogr[col][v].end());
            }
        }
        bool ok = dfs(1);
        if (timeout) return Status::TIMEOUT;
        return ok ? Status::DA_SIE : Status::NIE_DA_SIE;
    }
};

int testuj(const string& etykieta, const vector<Rownanie>& eqs, int prev, int max_n = 120, int limit_ms = 3000) {
    auto start = chrono::steady_clock::now();
    MultiRadoSolver solver(eqs);
    int wynik = -1, n_to = -1;
    bool to = false;

    for (int n = 1; n <= max_n; ++n) {
        Status st = solver.sprawdz(n, limit_ms);
        if (st == Status::NIE_DA_SIE) { wynik = n; break; }
        if (st == Status::TIMEOUT) { to = true; n_to = n; break; }
    }

    double ms = chrono::duration<double, milli>(chrono::steady_clock::now() - start).count();
    cout << left << setw(6) << etykieta << " | ";
    if (wynik != -1) {
        cout << "R = " << setw(3) << wynik;
        if (prev != -1) cout << " (+" << setw(2) << (wynik - prev) << ")";
        else cout << "      ";
        cout << " | " << fixed << setprecision(1) << ms << " ms\n";
    } else if (to) {
        cout << "[TIMEOUT przy N=" << n_to << "]\n";
    } else {
        cout << "[Brak do N=" << max_n << "]\n";
    }
    cout << flush;
    return wynik;
}

int main() {
    Rownanie ap3 = {1, 1, 0, 2, true};
    Rownanie eq123 = {1, 2, 0, 3, true};

    cout << "=== TEST 1 (2 kolory): (x + 2y = 3z) vs (x + a*y = z) ===\n";
    int prev = -1;
    for (int a = 1; a <= 8; ++a) {
        prev = testuj("a=" + to_string(a), {eq123, {1, a, 0, 1, false}}, prev);
        if (prev == -1) break;
    }

    cout << "\n=== TEST 2 (3 kolory): (3-AP) vs (3-AP) vs (x + a*y = z) ===\n";
    prev = -1;
    for (int a = 1; a <= 6; ++a) {
        prev = testuj("a=" + to_string(a), {ap3, ap3, {1, a, 0, 1, false}}, prev);
        if (prev == -1) break;
    }
    return 0;
}
