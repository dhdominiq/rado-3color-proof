#include <iostream>
#include <vector>
#include <algorithm>
#include <chrono>
#include <string>

using namespace std;

struct Rownanie {
    int a, b, c, d; // a*x + b*y + c = d*z
    bool rozne;
    string opis;
};

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

enum class Status { DA_SIE, NIE_DA_SIE, TIMEOUT };

class MultiRadoSolver {
    vector<Rownanie> eqs;
    bool symetryczne;
    int kolory;
    int N;
    vector<vector<vector<Para>>> ogr;
    vector<int> kolor;
    long long wezly;
    bool przekroczono_czas;
    chrono::steady_clock::time_point deadline;

    bool dfs(int v, int max_uzyty) {
        if (przekroczono_czas) return false;
        if ((++wezly & 4095) == 0) {
            if (chrono::steady_clock::now() > deadline) {
                przekroczono_czas = true;
                return false;
            }
        }
        if (v > N) return true;

        int limit = symetryczne ? min(max_uzyty + 1, kolory - 1) : (kolory - 1);
        for (int col = 0; col <= limit; ++col) {
            kolor[v] = col;
            bool konflikt = false;

            for (const auto& p : ogr[col][v]) {
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
    MultiRadoSolver(const vector<Rownanie>& eqs, bool symetryczne)
        : eqs(eqs), symetryczne(symetryczne), kolory((int)eqs.size()), N(0),
          wezly(0), przekroczono_czas(false) {}

    Status sprawdz(int n, vector<int>& zapisane_kolory, int limit_ms) {
        N = n;
        ogr.assign(kolory, vector<vector<Para>>(N + 1));
        kolor.assign(N + 1, -1);
        wezly = 0;
        przekroczono_czas = false;
        deadline = chrono::steady_clock::now() + chrono::milliseconds(limit_ms);

        for (int col = 0; col < kolory; ++col) {
            const auto& e = eqs[col];
            for (int x = 1; x <= N; ++x) {
                for (int y = 1; y <= N; ++y) {
                    long long lewa = 1LL * e.a * x + 1LL * e.b * y + e.c;
                    if (lewa <= 0 || lewa % e.d != 0) continue;
                    long long z_ll = lewa / e.d;
                    if (z_ll < 1 || z_ll > N) continue;
                    int z = static_cast<int>(z_ll);

                    if (e.rozne && (x == y || x == z || y == z)) continue;

                    int m = max(x, max(y, z));
                    int u, w;
                    if (m == x) { u = y; w = z; }
                    else if (m == y) { u = x; w = z; }
                    else { u = x; w = y; }

                    if (u > w) swap(u, w);
                    ogr[col][m].push_back({u, w});
                }
            }

            for (int v = 1; v <= N; ++v) {
                sort(ogr[col][v].begin(), ogr[col][v].end());
                ogr[col][v].erase(
                    unique(ogr[col][v].begin(), ogr[col][v].end()),
                    ogr[col][v].end()
                );
            }
        }

        bool ok = dfs(1, -1);
        if (przekroczono_czas) return Status::TIMEOUT;
        if (ok) {
            zapisane_kolory = kolor;
            return Status::DA_SIE;
        }
        return Status::NIE_DA_SIE;
    }
};

void skanuj_pare(const Rownanie& e1, const Rownanie& e2, int max_n = 150, int limit_ms = 3000) {
    auto start = chrono::steady_clock::now();
    MultiRadoSolver solver({e1, e2}, false);

    vector<int> ostatnie;
    int wynik = -1;
    bool timeout = false;
    int n_timeout = -1;

    for (int n = 1; n <= max_n; ++n) {
        vector<int> akt;
        Status st = solver.sprawdz(n, akt, limit_ms);
        if (st == Status::DA_SIE) {
            ostatnie = akt;
        } else if (st == Status::NIE_DA_SIE) {
            wynik = n;
            break;
        } else {
            timeout = true;
            n_timeout = n;
            break;
        }
    }

    auto koniec = chrono::steady_clock::now();
    double czas_ms = chrono::duration<double, milli>(koniec - start).count();

    cout << "[" << e1.opis << "] vs [" << e2.opis << "] -> ";
    if (wynik != -1) {
        cout << "R = " << wynik << " (" << czas_ms << " ms)\n";
    } else if (timeout) {
        cout << "[TIMEOUT przy N = " << n_timeout << "] (>=" << n_timeout << ")\n";
    } else {
        cout << "[Brak granicy do N = " << max_n << "]\n";
    }
    cout << flush;
}

int main() {
    Rownanie ap3 = {1, 1, 0, 2, true, "x+y=2z (rozne)"};

    cout << "=== RODZINA A: 3-AP vs x + a*y = z (powtorzenia dozwolone) ===\n";
    for (int a = 1; a <= 6; ++a) {
        Rownanie e2 = {1, a, 0, 1, false, "x+" + to_string(a) + "y=z"};
        skanuj_pare(ap3, e2);
    }

    cout << "\n=== RODZINA B: 3-AP vs x + a*y = z (liczby ROZNE) ===\n";
    for (int a = 1; a <= 6; ++a) {
        Rownanie e2 = {1, a, 0, 1, true, "x+" + to_string(a) + "y=z (rozne)"};
        skanuj_pare(ap3, e2);
    }

    cout << "\n=== RODZINA C: 3-AP vs x + y + c = z (liczby ROZNE) ===\n";
    for (int c = 0; c <= 6; ++c) {
        Rownanie e2 = {1, 1, c, 1, true, "x+y+" + to_string(c) + "=z (rozne)"};
        skanuj_pare(ap3, e2);
    }

    return 0;
}
