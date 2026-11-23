# O czym jest ten projekt? (proste wyjasnienie)

## Zasady gry
Bierzemy liczby od 1 do N i kazda malujemy na jeden z trzech kolorow: czerwony, zielony albo niebieski.
- W czerwonym i zielonym nie wolno ulozyc trzech liczb w rownych odstepach (np. 2, 5, 8).
- W niebieskim nie wolno ulozyc rownania x + a*y = z (gdzie a to wybrana liczba).

Pytanie brzmi: przy jakiej liczbie N na pewno przegrasz, jakkolwiek bys nie malowal?

## Co zostalo udowodnione?
Dla kazdej liczby a od 28 az do nieskonczonosci dokladna granica wynosi:

    R(a) = 9*a + 64

## Jak to zostalo sprawdzone?
1. Lean 4 (lean/Rado3Kolory.lean) - kompilator matematyczny potwierdzil bez zadnego bledu, ze:
   - dla 9a + 63 ZAWSZE istnieje dobre kolorowanie (podajemy gotowy przepis z 63-znakowego wzorca),
   - dla 9a + 64 ZAWSZE przegrywasz, o ile zachodza dwa skonczone fakty: znane W(3,4) = 76 oraz nowa stala K = 64.
2. Solver SAT + drat-trim (wyniki/K64.cnf, wyniki/09_drat_verified.txt) - solver CaDiCaL wygenerowal dowod dla K = 64 (ponad 3,6 mln krokow), a niezalezny program drat-trim sprawdzil 44,6 mln operacji i zwrocil s VERIFIED.
