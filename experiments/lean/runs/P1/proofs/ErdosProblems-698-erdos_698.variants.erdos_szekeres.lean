import Mathlib

/-! Formalization of `Erdos698.erdos_698.variants.erdos_szekeres`.
Erdős–Szekeres: gcd (C(n,i)) (C(n,j)) ≥ C(n,i)/C(j,i) ≥ 2^i for 1 ≤ i < j ≤ n/2. -/

theorem swarm_proof (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j)
    (hj : j ≤ n / 2) :
    (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) := by
  have hjn : j ≤ n := by omega
  have hin : i ≤ n := by omega
  have hfa : n.choose i * Nat.factorial i * Nat.factorial (n - i) = Nat.factorial n := Nat.choose_mul_factorial_mul_factorial hin
  have hfb : n.choose j * Nat.factorial j * Nat.factorial (n - j) = Nat.factorial n := Nat.choose_mul_factorial_mul_factorial hjn
  have hsub : n - i - (j - i) = n - j := by omega
  have hfc : (n - i).choose (j - i) * Nat.factorial (j - i) * Nat.factorial (n - j)
      = Nat.factorial (n - i) := by
    rw [← hsub]
    exact Nat.choose_mul_factorial_mul_factorial (by omega)
  have hfd : j.choose i * Nat.factorial i * Nat.factorial (j - i) = Nat.factorial j := Nat.choose_mul_factorial_mul_factorial (by omega)
  have hap : 0 < n.choose i := Nat.choose_pos hin
  have htp : 0 < j.choose i := Nat.choose_pos (by omega)
  -- the four-binomial identity  C(n,i) * C(n-i, j-i) = C(n,j) * C(j,i)
  have ident : n.choose i * (n - i).choose (j - i) = n.choose j * j.choose i := by
    have hMul : Nat.factorial i * Nat.factorial (j - i) * Nat.factorial (n - j) *
          (n.choose i * (n - i).choose (j - i))
        = Nat.factorial i * Nat.factorial (j - i) * Nat.factorial (n - j) *
          (n.choose j * j.choose i) := by
      calc Nat.factorial i * Nat.factorial (j - i) * Nat.factorial (n - j) *
            (n.choose i * (n - i).choose (j - i))
          = n.choose i * (Nat.factorial i *
              ((n - i).choose (j - i) * Nat.factorial (j - i) *
                Nat.factorial (n - j))) := by ring
        _ = n.choose i * (Nat.factorial i * Nat.factorial (n - i)) := by rw [hfc]
        _ = n.choose i * Nat.factorial i * Nat.factorial (n - i) := by ring
        _ = Nat.factorial n := hfa
        _ = n.choose j * Nat.factorial j * Nat.factorial (n - j) := hfb.symm
        _ = n.choose j * Nat.factorial (n - j) *
            (j.choose i * Nat.factorial i * Nat.factorial (j - i)) := by
              rw [← hfd]; ring
        _ = Nat.factorial i * Nat.factorial (j - i) * Nat.factorial (n - j) *
            (n.choose j * j.choose i) := by ring
    exact Nat.eq_of_mul_eq_mul_left
      (show 0 < Nat.factorial i * Nat.factorial (j - i) * Nat.factorial (n - j) by
        positivity) hMul
  -- part 1 : C(n,i) ∣ gcd * C(j,i)
  have hdiv : n.choose i ∣ Nat.gcd (n.choose i) (n.choose j) * j.choose i := by
    have hd0 : 0 < Nat.gcd (n.choose i) (n.choose j) := Nat.gcd_pos_of_pos_left _ hap
    have hdda : Nat.gcd (n.choose i) (n.choose j) ∣ n.choose i := Nat.gcd_dvd_left _ _
    have hddb : Nat.gcd (n.choose i) (n.choose j) ∣ n.choose j := Nat.gcd_dvd_right _ _
    have key : n.choose i / Nat.gcd (n.choose i) (n.choose j) * (n - i).choose (j - i)
        = n.choose j / Nat.gcd (n.choose i) (n.choose j) * j.choose i := by
      have h1 : Nat.gcd (n.choose i) (n.choose j) *
          (n.choose i / Nat.gcd (n.choose i) (n.choose j) * (n - i).choose (j - i))
          = Nat.gcd (n.choose i) (n.choose j) *
          (n.choose j / Nat.gcd (n.choose i) (n.choose j) * j.choose i) := by
        rw [← Nat.mul_assoc, ← Nat.mul_assoc,
          Nat.mul_div_cancel' hdda, Nat.mul_div_cancel' hddb]
        exact ident
      exact Nat.eq_of_mul_eq_mul_left hd0 h1
    have hcop : Nat.Coprime
        (n.choose i / Nat.gcd (n.choose i) (n.choose j))
        (n.choose j / Nat.gcd (n.choose i) (n.choose j)) := by
      set d := Nat.gcd (n.choose i) (n.choose j) with hddef
      set g := Nat.gcd (n.choose i / d) (n.choose j / d) with hgdef
      have hd0' : 0 < d := hd0
      have hgpos : 0 < g :=
        Nat.gcd_pos_of_pos_left _ (Nat.div_pos (Nat.le_of_dvd hap hdda) hd0')
      have h7 : d * g ∣ d * (n.choose i / d) :=
        Nat.mul_dvd_mul (Nat.dvd_refl d) (Nat.gcd_dvd_left (n.choose i / d) (n.choose j / d))
      have h8 : d * g ∣ d * (n.choose j / d) :=
        Nat.mul_dvd_mul (Nat.dvd_refl d) (Nat.gcd_dvd_right (n.choose i / d) (n.choose j / d))
      rw [Nat.mul_div_cancel' hdda] at h7
      rw [Nat.mul_div_cancel' hddb] at h8
      have h9 := Nat.dvd_gcd h7 h8
      rw [hddef] at h9
      have h10 : d * g ≤ d := Nat.le_of_dvd hd0' h9
      have h13 : g ≤ 1 :=
        Nat.le_of_mul_le_mul_left (by simpa using h10) hd0'
      exact Nat.le_antisymm h13 (by omega)
    have h5 : n.choose i / Nat.gcd (n.choose i) (n.choose j) ∣ j.choose i :=
      hcop.dvd_of_dvd_mul_left ⟨(n - i).choose (j - i), key.symm⟩
    calc n.choose i
        = Nat.gcd (n.choose i) (n.choose j) *
          (n.choose i / Nat.gcd (n.choose i) (n.choose j)) :=
          (Nat.mul_div_cancel' hdda).symm
      _ ∣ Nat.gcd (n.choose i) (n.choose j) * j.choose i :=
          Nat.mul_dvd_mul_left _ h5
  have hle : n.choose i ≤ Nat.gcd (n.choose i) (n.choose j) * j.choose i :=
    Nat.le_of_dvd (by positivity) hdiv
  -- part 2 : 2^k * C(j,k) ≤ C(n,k) by induction
  have pow2 : ∀ k, k ≤ j → 2 ^ k * j.choose k ≤ n.choose k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hkj : k ≤ j := by omega
      have ihl := ih hkj
      have hrj : j.choose (k + 1) * (k + 1) = j.choose k * (j - k) :=
        Nat.choose_succ_right_eq j k
      have hrn : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) :=
        Nat.choose_succ_right_eq n k
      have step : 2 ^ (k + 1) * j.choose (k + 1) * (k + 1) ≤ n.choose (k + 1) * (k + 1) := by
        calc 2 ^ (k + 1) * j.choose (k + 1) * (k + 1)
            = 2 * (2 ^ k * (j.choose (k + 1) * (k + 1))) := by ring
          _ = 2 * (2 ^ k * (j.choose k * (j - k))) := by rw [hrj]
          _ = (2 ^ k * j.choose k) * (2 * (j - k)) := by ring
          _ ≤ n.choose k * (2 * (j - k)) := Nat.mul_le_mul_right _ ihl
          _ ≤ n.choose k * (n - k) := Nat.mul_le_mul_left _ (by omega)
          _ = n.choose (k + 1) * (k + 1) := hrn.symm
      exact Nat.le_of_mul_le_mul_right step (by omega)
  have h2 := pow2 i (by omega)
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ (by exact_mod_cast htp)]
    exact_mod_cast hle
  · rw [le_div_iff₀ (by exact_mod_cast htp)]
    rw [show ((2:ℝ) ^ i) * (j.choose i : ℝ) = ((2 ^ i * j.choose i : ℕ) : ℝ) from by
      push_cast; ring]
    exact_mod_cast h2
