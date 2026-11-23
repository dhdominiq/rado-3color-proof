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
    int kolory;
    int N;
    vector<vector<vector<Para>>> ogr;
    vector<int> kolor;
    long long wezly;
    bool przekroczono_czas;
    chrono::steady_clock::time_point deadline;

    bool dfs(int v) {
        if (przekroczono_czas) return false;
        if ((++wezly & 4095) == 0) {
            if (chrono::steady_clock::now() > deadline) {
                przekroczono_czas = true;
                return false;
            }
        }
        if (v > N) return true;

        for (int col = 0; col < kolory; ++col) {
            kolor[v] = col;
            bool konflikt = false;
            for (const auto& p : ogr[col][v]) {
                if (kolor[p.u] == col && kolor[p.w] == col) {
                    konflikt = true;
                    break;
                }
            }
            if (!konflikt && dfs(v + 1)) return true;
        }
        return false;
    }

public:
    MultiRadoSolver(const vector<Rownanie>& eqs)
        : eqs(eqs), kolory((int)eqs.size()), N(0), wezly(0), przekroczono_czas(false) {}

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

        bool ok = dfs(1);
        if (przekroczono_czas) return Status::TIMEOUT;
        if (ok) {
            zapisane_kolory = kolor;
            return Status::DA_SIE;
        }
        return Status::NIE_DA_SIE;
    }
};

int uruchom_przypadek(const string& etykieta, const Rownanie& e1, const Rownanie& e2,
                      int poprzedni, bool pokaz_kolory, int max_n = 120, int limit_ms = 3000) {
    auto start = chrono::steady_clock::now();
    MultiRadoSolver solver({e1, e2});
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
    double ms = chrono::duration<double, milli>(koniec - start).count();

    cout << left << setw(8) << etykieta << " | ";
    if (wynik != -1) {
        cout << "R = " << setw(3) << wynik;
        if (poprzedni != -1) cout << " (+" << setw(2) << (wynik - poprzedni) << ")";
        else cout << "      ";
        cout << " | " << fixed << setprecision(1) << setw(6) << ms << " ms";
        if (pokaz_kolory) {
            cout << " | ";
            for (int i = 1; i < (int)ostatnie.size(); ++i) {
                cout << (ostatnie[i] == 0 ? 'C' : 'N');
            }
        }
        cout << "\n";
    } else if (timeout) {
        cout << "[TIMEOUT przy N=" << n_timeout << "]\n";
    } else {
        cout << "[Brak do N=" << max_n << "]\n";
    }
    cout << flush;
    return wynik;
}

int main() {
    Rownanie ap3 = {1, 1, 0, 2, true, "3-AP"};

    cout << "=== ZOOM A: 3-AP vs x + a*y = z (powtorzenia dozwolone) ===\n";
    int prev = -1;
    for (int a = 1; a <= 14; ++a) {
        Rownanie e2 = {1, a, 0, 1, false, ""};
        prev = uruchom_przypadek("a=" + to_string(a), ap3, e2, prev, true);
        if (prev == -1) break;
    }

    cout << "\n=== ZOOM B: 3-AP vs x + a*y = z (liczby ROZNE) ===\n";
    prev = -1;
    for (int a = 1; a <= 12; ++a) {
        Rownanie e2 = {1, a, 0, 1, true, ""};
        prev = uruchom_przypadek("a=" + to_string(a), ap3, e2, prev, false);
        if (prev == -1) break;
    }

    cout << "\n=== ZOOM C: 3-AP vs x + y + c = z (liczby ROZNE) ===\n";
    prev = -1;
    for (int c = 0; c <= 20; ++c) {
        Rownanie e2 = {1, 1, c, 1, true, ""};
        prev = uruchom_przypadek("c=" + to_string(c), ap3, e2, prev, true);
        if (prev == -1) break;
    }

    return 0;
}
