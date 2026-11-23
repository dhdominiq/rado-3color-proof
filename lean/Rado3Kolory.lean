/-
  Formalny dowód twierdzenia o 3-kolorowej asymetrycznej liczbie Rado:
  R(3-AP, 3-AP, x + a*y = z) = 9*a + 64 dla wszystkich a >= 28.
-/

inductive Color
  | C | Z | N
  deriving DecidableEq, Repr

/-- Brak ciągu arytmetycznego długości 3 w przedziale [1, bound] dla koloru c -/
def No3AP (bound : Nat) (col : Nat → Color) (c : Color) : Prop :=
  ∀ x d : Nat, 1 ≤ x → 1 ≤ d → x + 2 * d ≤ bound →
    ¬ (col x = c ∧ col (x + d) = c ∧ col (x + 2 * d) = c)

/-- Brak rozwiązania x + a*y = z w przedziale [1, bound] w kolorze N -/
def NoEqN (a bound : Nat) (col : Nat → Color) : Prop :=
  ∀ x y z : Nat, 1 ≤ x → 1 ≤ y → 1 ≤ z → z ≤ bound → x + a * y = z →
    ¬ (col x = Color.N ∧ col y = Color.N ∧ col z = Color.N)

/-- Poprawne 3-kolorowanie przedziału [1, bound] dla parametru a -/
def ValidColoring (a bound : Nat) (col : Nat → Color) : Prop :=
  No3AP bound col Color.C ∧ No3AP bound col Color.Z ∧ NoEqN a bound col

/-- 4-kolorowanie [1, bound] bez 3-AP w żadnym z 4 kolorów (0, 1, 2, 3) -/
def Valid4AP (bound : Nat) (f : Nat → Nat) : Prop :=
  (∀ x : Nat, 1 ≤ x → x ≤ bound → f x < 4) ∧
  (∀ x d : Nat, 1 ≤ x → 1 ≤ d → x + 2 * d ≤ bound →
    ¬ (f x = f (x + d) ∧ f x = f (x + 2 * d)))

/-- Ograniczone 4-kolorowanie [1, bound]: liczby 1..8 mają tylko kolory 0 lub 1 -/
def ValidRestricted4AP (bound : Nat) (f : Nat → Nat) : Prop :=
  Valid4AP bound f ∧ (∀ x : Nat, 1 ≤ x → x ≤ 8 → f x < 2)

-- ============================================================================
-- CZĘŚĆ 1: DOLNA GRANICA (dla każdego a >= 28 istnieje poprawne kolorowanie 9a+63)
-- ============================================================================

def patList : List Nat :=
  [0,1,1,0,0,1,1,0,2,0,
   3,3,0,1,3,1,1,2,1,0,
   2,2,0,3,2,3,3,0,0,2,
   2,3,1,3,3,2,0,1,1,0,
   1,1,2,0,3,2,0,2,0,3,
   3,2,1,3,1,1,2,1,2,3,
   3,0,0]

def listGet : List Nat → Nat → Nat
  | [], _ => 0
  | h :: _, 0 => h
  | _ :: t, n + 1 => listGet t n

def pat (i : Nat) : Nat := listGet patList (i - 1)

theorem pat_no_3ap_fin :
    ∀ x : Fin 63, ∀ d : Fin 32,
      1 ≤ d.val → x.val + 1 + 2 * d.val ≤ 63 →
        ¬ (pat (x.val + 1) = pat (x.val + 1 + d.val) ∧
           pat (x.val + 1) = pat (x.val + 1 + 2 * d.val)) := by
  decide

theorem pat_no_3ap (x d : Nat) (hx : 1 ≤ x) (hd : 1 ≤ d) (hbound : x + 2 * d ≤ 63) :
    ¬ (pat x = pat (x + d) ∧ pat x = pat (x + 2 * d)) := by
  have h := pat_no_3ap_fin ⟨x - 1, by omega⟩ ⟨d, by omega⟩ (by dsimp; omega) (by dsimp; omega)
  dsimp only at h
  have h1 : x - 1 + 1 = x := by omega
  simp only [h1] at h
  exact h

theorem pat_small_fin : ∀ x : Fin 8, pat (x.val + 1) < 2 := by decide

theorem pat_small (x : Nat) (hx1 : 1 ≤ x) (hx8 : x ≤ 8) : pat x < 2 := by
  have h := pat_small_fin ⟨x - 1, by omega⟩
  dsimp only at h
  have h1 : x - 1 + 1 = x := by omega
  rw [h1] at h
  exact h

theorem pat_lt_4_fin : ∀ x : Fin 63, pat (x.val + 1) < 4 := by decide

theorem pat_lt_4 (x : Nat) (hx1 : 1 ≤ x) (hx63 : x ≤ 63) : pat x < 4 := by
  have h := pat_lt_4_fin ⟨x - 1, by omega⟩
  dsimp only at h
  have h1 : x - 1 + 1 = x := by omega
  rw [h1] at h
  exact h

theorem pat_10 : pat 10 = 0 := by decide

/-- Nasza jawna konstrukcja 3-kolorowania przedziału [1, 9*a + 63] -/
def col3 (a : Nat) (x : Nat) : Color :=
  if x ≤ 63 then
    match pat x with
    | 0 => Color.C
    | 1 => Color.Z
    | _ => Color.N
  else if x ≤ 9 * a then
    Color.N
  else
    match pat (x - 9 * a) with
    | 2 => Color.C
    | 3 => Color.Z
    | _ => Color.N

theorem col3_not_N_range {a u : Nat} (h : col3 a u ≠ Color.N) : u ≤ 63 ∨ 9 * a < u := by
  by_cases h1 : u ≤ 63
  · exact Or.inl h1
  · by_cases h2 : u ≤ 9 * a
    · exfalso
      apply h
      unfold col3
      simp [h1, h2]
    · exact Or.inr (by omega)

theorem col3_low_C {a u : Nat} (hu1 : 1 ≤ u) (hu63 : u ≤ 63) (hc : col3 a u = Color.C) : pat u = 0 := by
  have hlt := pat_lt_4 u hu1 hu63
  unfold col3 at hc
  split at hc
  · rcases (by omega : pat u = 0 ∨ pat u = 1 ∨ pat u = 2 ∨ pat u = 3) with h0 | h1 | h2 | h3
    · exact h0
    · rw [h1] at hc; cases hc
    · rw [h2] at hc; cases hc
    · rw [h3] at hc; cases hc
  · omega

theorem col3_low_Z {a u : Nat} (hu1 : 1 ≤ u) (hu63 : u ≤ 63) (hc : col3 a u = Color.Z) : pat u = 1 := by
  have hlt := pat_lt_4 u hu1 hu63
  unfold col3 at hc
  split at hc
  · rcases (by omega : pat u = 0 ∨ pat u = 1 ∨ pat u = 2 ∨ pat u = 3) with h0 | h1 | h2 | h3
    · rw [h0] at hc; cases hc
    · exact h1
    · rw [h2] at hc; cases hc
    · rw [h3] at hc; cases hc
  · omega

theorem col3_high_C {a u : Nat} (ha : a ≥ 28) (hu1 : 9 * a < u) (hu2 : u ≤ 9 * a + 63)
    (hc : col3 a u = Color.C) : pat (u - 9 * a) = 2 := by
  have hlt := pat_lt_4 (u - 9 * a) (by omega) (by omega)
  unfold col3 at hc
  split at hc
  · omega
  · split at hc
    · omega
    · rcases (by omega : pat (u - 9 * a) = 0 ∨ pat (u - 9 * a) = 1 ∨ pat (u - 9 * a) = 2 ∨ pat (u - 9 * a) = 3) with h0 | h1 | h2 | h3
      · rw [h0] at hc; cases hc
      · rw [h1] at hc; cases hc
      · exact h2
      · rw [h3] at hc; cases hc

theorem col3_high_Z {a u : Nat} (ha : a ≥ 28) (hu1 : 9 * a < u) (hu2 : u ≤ 9 * a + 63)
    (hc : col3 a u = Color.Z) : pat (u - 9 * a) = 3 := by
  have hlt := pat_lt_4 (u - 9 * a) (by omega) (by omega)
  unfold col3 at hc
  split at hc
  · omega
  · split at hc
    · omega
    · rcases (by omega : pat (u - 9 * a) = 0 ∨ pat (u - 9 * a) = 1 ∨ pat (u - 9 * a) = 2 ∨ pat (u - 9 * a) = 3) with h0 | h1 | h2 | h3
      · rw [h0] at hc; cases hc
      · rw [h1] at hc; cases hc
      · rw [h2] at hc; cases hc
      · exact h3

theorem col3_no_3ap_C (a : Nat) (ha : a ≥ 28) : No3AP (9 * a + 63) (col3 a) Color.C := by
  intro x d hx hd hbound ⟨h1, h2, h3⟩
  have rx  := col3_not_N_range (by rw [h1]; decide : col3 a x ≠ Color.N)
  have rxd := col3_not_N_range (by rw [h2]; decide : col3 a (x + d) ≠ Color.N)
  have rx2 := col3_not_N_range (by rw [h3]; decide : col3 a (x + 2 * d) ≠ Color.N)
  rcases rxd with hlow | hhigh
  · have h2d : x + 2 * d ≤ 63 := by omega
    have p1 := col3_low_C hx (by omega) h1
    have p2 := col3_low_C (by omega) hlow h2
    have p3 := col3_low_C (by omega) h2d h3
    exact pat_no_3ap x d hx hd h2d ⟨by rw [p1, p2], by rw [p1, p3]⟩
  · have hx_hi : 9 * a < x := by omega
    have p1 := col3_high_C ha hx_hi (by omega) h1
    have p2 := col3_high_C ha hhigh (by omega) h2
    have p3 := col3_high_C ha (by omega) hbound h3
    have e1 : x + d - 9 * a = (x - 9 * a) + d := by omega
    have e2 : x + 2 * d - 9 * a = (x - 9 * a) + 2 * d := by omega
    rw [e1] at p2
    rw [e2] at p3
    exact pat_no_3ap (x - 9 * a) d (by omega) hd (by omega) ⟨by rw [p1, p2], by rw [p1, p3]⟩

theorem col3_no_3ap_Z (a : Nat) (ha : a ≥ 28) : No3AP (9 * a + 63) (col3 a) Color.Z := by
  intro x d hx hd hbound ⟨h1, h2, h3⟩
  have rx  := col3_not_N_range (by rw [h1]; decide : col3 a x ≠ Color.N)
  have rxd := col3_not_N_range (by rw [h2]; decide : col3 a (x + d) ≠ Color.N)
  have rx2 := col3_not_N_range (by rw [h3]; decide : col3 a (x + 2 * d) ≠ Color.N)
  rcases rxd with hlow | hhigh
  · have h2d : x + 2 * d ≤ 63 := by omega
    have p1 := col3_low_Z hx (by omega) h1
    have p2 := col3_low_Z (by omega) hlow h2
    have p3 := col3_low_Z (by omega) h2d h3
    exact pat_no_3ap x d hx hd h2d ⟨by rw [p1, p2], by rw [p1, p3]⟩
  · have hx_hi : 9 * a < x := by omega
    have p1 := col3_high_Z ha hx_hi (by omega) h1
    have p2 := col3_high_Z ha hhigh (by omega) h2
    have p3 := col3_high_Z ha (by omega) hbound h3
    have e1 : x + d - 9 * a = (x - 9 * a) + d := by omega
    have e2 : x + 2 * d - 9 * a = (x - 9 * a) + 2 * d := by omega
    rw [e1] at p2
    rw [e2] at p3
    exact pat_no_3ap (x - 9 * a) d (by omega) hd (by omega) ⟨by rw [p1, p2], by rw [p1, p3]⟩

theorem col3_no_eq_N (a : Nat) (ha : a ≥ 28) : NoEqN a (9 * a + 63) (col3 a) := by
  intro x y z hx1 hy1 hz1 hzb heq ⟨hcx, hcy, hcz⟩
  have hx9 : 9 ≤ x := by
    by_cases hx8 : x ≤ 8
    · exfalso
      have hlt := pat_small x hx1 hx8
      unfold col3 at hcx
      split at hcx
      · rcases (by omega : pat x = 0 ∨ pat x = 1) with h0 | h1
        · rw [h0] at hcx; cases hcx
        · rw [h1] at hcx; cases hcx
      · omega
    · omega
  have hy9 : 9 ≤ y := by
    by_cases hy8 : y ≤ 8
    · exfalso
      have hlt := pat_small y hy1 hy8
      unfold col3 at hcy
      split at hcy
      · rcases (by omega : pat y = 0 ∨ pat y = 1) with h0 | h1
        · rw [h0] at hcy; cases hcy
        · rw [h1] at hcy; cases hcy
      · omega
    · omega
  have hy10 : y ≠ 10 := by
    intro h10
    rw [h10] at hcy
    unfold col3 at hcy
    split at hcy
    · rw [pat_10] at hcy; cases hcy
    · omega
  rcases (by omega : y = 9 ∨ 11 ≤ y) with hy_eq9 | hy11
  · subst hy_eq9
    have hx63 : x ≤ 63 := by omega
    have hpx4 := pat_lt_4 x hx1 hx63
    unfold col3 at hcx
    split at hcx
    · unfold col3 at hcz
      split at hcz
      · omega
      · split at hcz
        · omega
        · have hsub : z - 9 * a = x := by omega
          rw [hsub] at hcz
          rcases (by omega : pat x = 0 ∨ pat x = 1 ∨ pat x = 2 ∨ pat x = 3) with h0 | h1 | h2 | h3
          · rw [h0] at hcx; cases hcx
          · rw [h1] at hcx; cases hcx
          · rw [h2] at hcz; cases hcz
          · rw [h3] at hcz; cases hcz
    · omega
  · have hmul : a * 11 ≤ a * y := Nat.mul_le_mul_left a hy11
    omega

theorem lower_bound (a : Nat) (ha : a ≥ 28) :
    ∃ col : Nat → Color, ValidColoring a (9 * a + 63) col :=
  ⟨col3 a, col3_no_3ap_C a ha, col3_no_3ap_Z a ha, col3_no_eq_N a ha⟩

-- ============================================================================
-- CZĘŚĆ 2: GÓRNA GRANICA (redukcja z W(3,4) = 76 oraz K = 64)
-- ============================================================================

def isC : Color → Bool
  | Color.C => true
  | _ => false

theorem w32_bool : ∀ b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b1 = b2 ∧ b2 = b3) ∨ (b2 = b3 ∧ b3 = b4) ∨ (b3 = b4 ∧ b4 = b5) ∨
    (b4 = b5 ∧ b5 = b6) ∨ (b5 = b6 ∧ b6 = b7) ∨ (b6 = b7 ∧ b7 = b8) ∨
    (b7 = b8 ∧ b8 = b9) ∨ (b1 = b3 ∧ b3 = b5) ∨ (b2 = b4 ∧ b4 = b6) ∨
    (b3 = b5 ∧ b5 = b7) ∨ (b4 = b6 ∧ b6 = b8) ∨ (b5 = b7 ∧ b7 = b9) ∨
    (b1 = b4 ∧ b4 = b7) ∨ (b2 = b5 ∧ b5 = b8) ∨ (b3 = b6 ∧ b6 = b9) ∨
    (b1 = b5 ∧ b5 = b9) := by
  decide

theorem triple_contra {bound : Nat} {col : Nat → Color}
    (hC : No3AP bound col Color.C) (hZ : No3AP bound col Color.Z)
    (hnoN : ∀ i, 1 ≤ i → i ≤ 9 → col i ≠ Color.N)
    {x d : Nat} (hx1 : 1 ≤ x) (hd1 : 1 ≤ d) (hx9 : x + 2 * d ≤ 9) (hb9 : 9 ≤ bound)
    (heq : isC (col x) = isC (col (x + d)) ∧ isC (col (x + d)) = isC (col (x + 2 * d))) :
    False := by
  have hxN := hnoN x hx1 (by omega)
  have hxdN := hnoN (x + d) (by omega) (by omega)
  have hx2dN := hnoN (x + 2 * d) (by omega) (by omega)
  cases h1 : col x <;> cases h2 : col (x + d) <;> cases h3 : col (x + 2 * d) <;>
    simp [isC, h1, h2, h3] at heq hxN hxdN hx2dN
  · exact hC x d hx1 hd1 (by omega) ⟨h1, h2, h3⟩
  · exact hZ x d hx1 hd1 (by omega) ⟨h1, h2, h3⟩

theorem w32_color {bound : Nat} {col : Nat → Color}
    (hC : No3AP bound col Color.C) (hZ : No3AP bound col Color.Z)
    (hb9 : 9 ≤ bound) (hnoN : ∀ i, 1 ≤ i → i ≤ 9 → col i ≠ Color.N) : False := by
  have h := w32_bool (isC (col 1)) (isC (col 2)) (isC (col 3))
                     (isC (col 4)) (isC (col 5)) (isC (col 6))
                     (isC (col 7)) (isC (col 8)) (isC (col 9))
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact triple_contra hC hZ hnoN (x := 1) (d := 1) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 2) (d := 1) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 3) (d := 1) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 4) (d := 1) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 5) (d := 1) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 6) (d := 1) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 7) (d := 1) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 1) (d := 2) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 2) (d := 2) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 3) (d := 2) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 4) (d := 2) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 5) (d := 2) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 1) (d := 3) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 2) (d := 3) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 3) (d := 3) (by omega) (by omega) (by omega) hb9 h
  · exact triple_contra hC hZ hnoN (x := 1) (d := 4) (by omega) (by omega) (by omega) hb9 h

def lift4 (a y0 : Nat) (col : Nat → Color) (x : Nat) : Nat :=
  match col x with
  | Color.C => 0
  | Color.Z => 1
  | Color.N =>
    match col (x + a * y0) with
    | Color.C => 2
    | _       => 3

theorem lift4_eq_0 {a y0 u : Nat} {col : Nat → Color} (hf : lift4 a y0 col u = 0) :
    col u = Color.C := by
  unfold lift4 at hf
  cases hcu : col u with
  | C => rfl
  | Z => rw [hcu] at hf; simp at hf
  | N => rw [hcu] at hf; cases hcu2 : col (u + a * y0) <;> (rw [hcu2] at hf; simp at hf)

theorem lift4_eq_1 {a y0 u : Nat} {col : Nat → Color} (hf : lift4 a y0 col u = 1) :
    col u = Color.Z := by
  unfold lift4 at hf
  cases hcu : col u with
  | C => rw [hcu] at hf; simp at hf
  | Z => rfl
  | N => rw [hcu] at hf; cases hcu2 : col (u + a * y0) <;> (rw [hcu2] at hf; simp at hf)

theorem lift4_eq_2 {a y0 u : Nat} {col : Nat → Color} (hf : lift4 a y0 col u = 2) :
    col (u + a * y0) = Color.C := by
  unfold lift4 at hf
  cases hcu : col u with
  | C => rw [hcu] at hf; simp at hf
  | Z => rw [hcu] at hf; simp at hf
  | N =>
    rw [hcu] at hf
    cases hcu2 : col (u + a * y0) with
    | C => rfl
    | Z => rw [hcu2] at hf; simp at hf
    | N => rw [hcu2] at hf; simp at hf

theorem lift4_eq_3 {a bound y0 u : Nat} {col : Nat → Color}
    (hN : NoEqN a bound col) (hu1 : 1 ≤ u) (hy1 : 1 ≤ y0)
    (hub : u + a * y0 ≤ bound) (hyN : col y0 = Color.N)
    (hf : lift4 a y0 col u = 3) : col (u + a * y0) = Color.Z := by
  unfold lift4 at hf
  cases hcu : col u with
  | C => rw [hcu] at hf; simp at hf
  | Z => rw [hcu] at hf; simp at hf
  | N =>
    rw [hcu] at hf
    cases hcu2 : col (u + a * y0) with
    | C => rw [hcu2] at hf; simp at hf
    | Z => rfl
    | N => exact False.elim (hN u y0 (u + a * y0) hu1 hy1 (by omega) hub rfl ⟨hcu, hyN, hcu2⟩)

theorem shifted_4ap {a bound y0 m : Nat} {col : Nat → Color}
    (hvalid : ValidColoring a bound col)
    (hy1 : 1 ≤ y0) (hyN : col y0 = Color.N)
    (hm : m + a * y0 ≤ bound) :
    Valid4AP m (lift4 a y0 col) := by
  constructor
  · intro x _ _
    unfold lift4
    cases col x
    · simp
    · simp
    · cases col (x + a * y0) <;> simp
  · intro x d hx hd hxd ⟨he1, he2⟩
    have hlt : lift4 a y0 col x < 4 := by
      unfold lift4
      cases col x
      · simp
      · simp
      · cases col (x + a * y0) <;> simp
    rcases (by omega : lift4 a y0 col x = 0 ∨ lift4 a y0 col x = 1 ∨
                       lift4 a y0 col x = 2 ∨ lift4 a y0 col x = 3) with h0 | h1 | h2 | h3
    · exact hvalid.1 x d hx hd (by omega)
        ⟨lift4_eq_0 h0,
         lift4_eq_0 (by omega : lift4 a y0 col (x + d) = 0),
         lift4_eq_0 (by omega : lift4 a y0 col (x + 2 * d) = 0)⟩
    · exact hvalid.2.1 x d hx hd (by omega)
        ⟨lift4_eq_1 h1,
         lift4_eq_1 (by omega : lift4 a y0 col (x + d) = 1),
         lift4_eq_1 (by omega : lift4 a y0 col (x + 2 * d) = 1)⟩
    · have c1 := lift4_eq_2 h2
      have c2 := lift4_eq_2 (by omega : lift4 a y0 col (x + d) = 2)
      have c3 := lift4_eq_2 (by omega : lift4 a y0 col (x + 2 * d) = 2)
      have e1 : x + d + a * y0 = (x + a * y0) + d := by omega
      have e2 : x + 2 * d + a * y0 = (x + a * y0) + 2 * d := by omega
      rw [e1] at c2; rw [e2] at c3
      exact hvalid.1 (x + a * y0) d (by omega) hd (by omega) ⟨c1, c2, c3⟩
    · have c1 := lift4_eq_3 hvalid.2.2 hx hy1 (by omega) hyN h3
      have c2 := lift4_eq_3 hvalid.2.2 (by omega) hy1 (by omega) hyN (by omega : lift4 a y0 col (x + d) = 3)
      have c3 := lift4_eq_3 hvalid.2.2 (by omega) hy1 (by omega) hyN (by omega : lift4 a y0 col (x + 2 * d) = 3)
      have e1 : x + d + a * y0 = (x + a * y0) + d := by omega
      have e2 : x + 2 * d + a * y0 = (x + a * y0) + 2 * d := by omega
      rw [e1] at c2; rw [e2] at c3
      exact hvalid.2.1 (x + a * y0) d (by omega) hd (by omega) ⟨c1, c2, c3⟩

theorem upper_bound (a : Nat) (ha : a ≥ 12)
    (hW34 : ¬ ∃ f, Valid4AP 76 f)
    (hK64 : ¬ ∃ f, ValidRestricted4AP 64 f) :
    ¬ ∃ col : Nat → Color, ValidColoring a (9 * a + 64) col := by
  intro ⟨col, hvalid⟩
  by_cases h1 : col 1 = Color.N
  · exact hW34 ⟨lift4 a 1 col, shifted_4ap hvalid (by omega) h1 (by omega)⟩
  by_cases h2 : col 2 = Color.N
  · exact hW34 ⟨lift4 a 2 col, shifted_4ap hvalid (by omega) h2 (by omega)⟩
  by_cases h3 : col 3 = Color.N
  · exact hW34 ⟨lift4 a 3 col, shifted_4ap hvalid (by omega) h3 (by omega)⟩
  by_cases h4 : col 4 = Color.N
  · exact hW34 ⟨lift4 a 4 col, shifted_4ap hvalid (by omega) h4 (by omega)⟩
  by_cases h5 : col 5 = Color.N
  · exact hW34 ⟨lift4 a 5 col, shifted_4ap hvalid (by omega) h5 (by omega)⟩
  by_cases h6 : col 6 = Color.N
  · exact hW34 ⟨lift4 a 6 col, shifted_4ap hvalid (by omega) h6 (by omega)⟩
  by_cases h7 : col 7 = Color.N
  · exact hW34 ⟨lift4 a 7 col, shifted_4ap hvalid (by omega) h7 (by omega)⟩
  by_cases h8 : col 8 = Color.N
  · exact hW34 ⟨lift4 a 8 col, shifted_4ap hvalid (by omega) h8 (by omega)⟩
  by_cases h9 : col 9 = Color.N
  · refine hK64 ⟨lift4 a 9 col, shifted_4ap hvalid (by omega) h9 (by omega), ?_⟩
    intro x hx1 hx8
    have hxN : col x ≠ Color.N := by
      rcases (by omega : x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    unfold lift4
    cases hcx : col x with
    | C => simp
    | Z => simp
    | N => exact False.elim (hxN hcx)
  · apply w32_color hvalid.1 hvalid.2.1 (by omega)
    intro i hi1 hi9
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

-- ============================================================================
-- GŁÓWNE TWIERDZENIE
-- ============================================================================

theorem main_theorem (a : Nat) (ha : a ≥ 28)
    (hW34 : ¬ ∃ f, Valid4AP 76 f)
    (hK64 : ¬ ∃ f, ValidRestricted4AP 64 f) :
    (∃ col : Nat → Color, ValidColoring a (9 * a + 63) col) ∧
    (¬ ∃ col : Nat → Color, ValidColoring a (9 * a + 64) col) :=
  ⟨lower_bound a ha, upper_bound a (by omega) hW34 hK64⟩

#check main_theorem
#print axioms main_theorem
