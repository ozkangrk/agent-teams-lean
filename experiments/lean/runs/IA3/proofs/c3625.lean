import FormalConjectures.OEIS.«3625»
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

open Polynomial

theorem two_ne_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  apply hp2
  have hd : (p : ℤ) ∣ (2 : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp (by push_cast; exact h)
  have hdn : p ∣ 2 := Int.natCast_dvd_natCast.mp hd
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdn
  have := hp.two_le
  omega

theorem root_not_irr {F : Type*} [Field F] (x : F) (hx : x ^ 2 + x + 2 = 0) :
    ¬Irreducible (X ^ 2 + X + 2 : F[X]) := by
  intro hirr
  have hc2 : (2 : F[X]) = C (2 : F) := rfl
  have hfac : (X - C x) * (X - C (-(x + 1))) = (X ^ 2 + X + 2 : F[X]) := by
    have h1 : (X - C x) * (X - C (-(x + 1))) = X ^ 2 + X - (C x * C x + C x) := by
      simp only [map_neg, map_add, map_one]
      ring
    rw [h1]
    have hC : C x * C x + C x = C (x * x + x) := by rw [← map_mul, ← map_add]
    rw [hC]
    have h2 : x ^ 2 = x * x := pow_two x
    rw [h2] at hx
    have hxx : x * x + x = -(2 : F) := by linear_combination hx
    rw [hxx, hc2]
    simp only [map_neg]
    ring
  rcases hirr.isUnit_or_isUnit hfac.symm with h | h
  · exact absurd (Polynomial.isUnit_iff_degree_eq_zero.mp h) (by
        rw [Polynomial.degree_X_sub_C]; norm_num)
  · exact absurd (Polynomial.isUnit_iff_degree_eq_zero.mp h) (by
        rw [Polynomial.degree_X_sub_C]; norm_num)

theorem root_of_red {F : Type*} [Field F] (hred : ¬ Irreducible (X ^ 2 + X + 2 : F[X])) :
    ∃ x : F, x ^ 2 + x + 2 = 0 := by
  have hc2 : (2 : F[X]) = C (2 : F) := rfl
  have hs : (X ^ 2 + X + 2 : F[X]) = X ^ 2 + (X + C (2 : F)) := by rw [hc2]; ring
  have hdegf : (X ^ 2 + X + 2 : F[X]).degree = 2 := by
    rw [hs, Polynomial.degree_add_eq_left_of_degree_lt (by
      rw [Polynomial.degree_X_pow, Polynomial.degree_X_add_C]; decide),
      Polynomial.degree_X_pow]
    decide
  have hfunit : ¬ IsUnit (X ^ 2 + X + 2 : F[X]) := fun h => by
    rw [Polynomial.isUnit_iff_degree_eq_zero] at h
    rw [hdegf] at h
    exact absurd h (by decide)
  obtain ⟨a, b, hau, hbu, hfab⟩ := (irreducible_or_factor hfunit).resolve_left hred
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at hfab
    have h2 : (X ^ 2 + X + 2 : F[X]).degree = (0 : F[X]).degree := by rw [hfab]; simp
    rw [hdegf, Polynomial.degree_zero] at h2
    exact absurd h2 (by decide)
  have hb0 : b ≠ 0 := by
    intro h
    rw [h] at hfab
    have h2 : (X ^ 2 + X + 2 : F[X]).degree = (0 : F[X]).degree := by rw [hfab]; simp
    rw [hdegf, Polynomial.degree_zero] at h2
    exact absurd h2 (by decide)
  have key : ∀ q : F[X], q ≠ 0 → ¬IsUnit q → 1 ≤ q.natDegree := by
    intro q q0 hq
    rcases Nat.eq_zero_or_pos q.natDegree with h0 | h0
    · exfalso
      have hd0 : q.degree = 0 := by
        rw [Polynomial.degree_eq_natDegree q0, h0]; norm_num
      have hqc := Polynomial.eq_C_of_degree_eq_zero hd0
      rw [hqc] at q0 hq
      exact hq (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Polynomial.C_ne_zero.mp q0)))
    · exact h0
  have hnd : a.natDegree + b.natDegree = 2 := by
    have hd2 : (a * b).degree = 2 := by rw [← hfab]; exact hdegf
    rw [Polynomial.degree_mul] at hd2
    have ha1 := key a ha0 hau
    have hb1 := key b hb0 hbu
    have hd3 : ((a.natDegree + b.natDegree : ℕ) : WithBot ℕ) = 2 := by
      rw [Nat.cast_add]
      rw [Polynomial.degree_eq_natDegree ha0, Polynomial.degree_eq_natDegree hb0] at hd2
      exact hd2
    exact Nat.cast_injective hd3
  have hda1 : a.natDegree = 1 := by
    have ha1 := key a ha0 hau
    have hb1 := key b hb0 hbu
    omega
  have hdeg1 : a.degree = 1 := by
    rw [Polynomial.degree_eq_natDegree ha0, hda1]
    decide
  obtain ⟨r, hr⟩ := Polynomial.exists_root_of_degree_eq_one hdeg1
  refine ⟨r, ?_⟩
  have hEval : (X ^ 2 + X + 2 : F[X]).eval r = a.eval r * b.eval r := by
    rw [hfab]; simp
  rw [hr, zero_mul] at hEval
  simpa using hEval

theorem sq_iff_root {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsSquare ((-7 : ℤ) : ZMod p) ↔ ∃ x : ZMod p, x ^ 2 + x + 2 = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zmod hp hp2
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨2⁻¹ * (y - 1), ?_⟩
    have h4 : (4 : ZMod p) * ((2⁻¹ * (y - 1)) ^ 2 + 2⁻¹ * (y - 1) + 2) = y * y + 7 := by
      field_simp
      ring
    have h0 : (4 : ZMod p) * ((2⁻¹ * (y - 1)) ^ 2 + 2⁻¹ * (y - 1) + 2) = 0 := by
      rw [h4, ← hy]
      push_cast
      ring
    rcases mul_eq_zero.mp h0 with h4z | hroot
    · exfalso
      have h22 : (2 : ZMod p) * 2 = 0 := by
        rw [show (2 : ZMod p) * 2 = (4 : ZMod p) from by norm_num]
        exact h4z
      rcases mul_eq_zero.mp h22 with h | h
      · exact h2ne h
      · exact h2ne h
    · exact hroot
  · rintro ⟨x, hx⟩
    refine ⟨2 * x + 1, ?_⟩
    have hc : ((-7 : ℤ) : ZMod p) = (0 - 7) := by push_cast; ring
    rw [hc]
    linear_combination (-4 : ZMod p) * hx

theorem sq_m7 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp7 : p ≠ 7) :
    IsSquare ((-7 : ℤ) : ZMod p) ↔ IsSquare ((p : ℕ) : ZMod 7) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (7 : ℕ).Prime := ⟨by norm_num⟩
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zmod hp hp2
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
    rcases Nat.Prime.eq_two_or_odd hp with rfl | hodd
    · exact absurd rfl hp2
    · omega
  have h7ne : ((7 : ℤ) : ZMod p) ≠ 0 := by
    intro h
    apply hp7
    have hd : (p : ℤ) ∣ (7 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (7 : ℤ) p).mp h
    have hdn : p ∣ 7 := Int.natCast_dvd_natCast.mp hd
    rcases (Nat.dvd_prime (show (7 : ℕ).Prime by norm_num)).mp hdn with h1 | h7eq
    · exact absurd h1 hp.ne_one
    · exact h7eq
  have h1ne : ((-1 : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have hc : ((-1 : ℤ) : ZMod p) = -1 := by push_cast; simp
    rw [hc] at h
    have h1z : ((1 : ℤ) : ZMod p) = 0 := by push_cast; exact neg_eq_zero.mp h
    have hd : (p : ℤ) ∣ (1 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (1 : ℤ) p).mp h1z
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hd) with hpe | hpe
    · exact hp.ne_one (Int.natCast_inj.mp hpe)
    · exact absurd hpe (by have := Int.natCast_nonneg p; omega)
  have h7mne : ((-7 : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have hc : ((-7 : ℤ) : ZMod p) = -((7 : ℤ) : ZMod p) := by push_cast; simp
    rw [hc] at h
    exact h7ne (neg_eq_zero.mp h)
  have hmul : legendreSym p (-7 : ℤ) = legendreSym p (-1 : ℤ) * legendreSym p (7 : ℤ) := by
    rw [show (-7 : ℤ) = (-1 : ℤ) * (7 : ℤ) from by ring]
    exact legendreSym.mul p _ _
  have hcard : Fintype.card (ZMod p) = p := by simp
  rcases hp4 with hp4 | hp4
  · have hn1 : legendreSym p (-1 : ℤ) = 1 := by
      refine (legendreSym.eq_one_iff p h1ne).mpr ?_
      have hc : ((-1 : ℤ) : ZMod p) = -1 := by push_cast; simp
      rw [hc]
      refine (FiniteField.isSquare_neg_one_iff).mpr ?_
      rw [hcard]
      omega
    have hq7 : IsSquare ((7 : ℕ) : ZMod p) ↔ IsSquare ((p : ℕ) : ZMod 7) :=
      ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hp4 (by norm_num)
    have hbridge : IsSquare ((7 : ℤ) : ZMod p) ↔ IsSquare ((7 : ℕ) : ZMod p) := by
      have hc : ((7 : ℤ) : ZMod p) = ((7 : ℕ) : ZMod p) := by push_cast; simp
      rw [hc]
    constructor
    · intro hsq
      have h1 : legendreSym p (-7 : ℤ) = 1 := (legendreSym.eq_one_iff p h7mne).mpr hsq
      rw [hmul, hn1, one_mul] at h1
      exact hq7.mp (hbridge.mp ((legendreSym.eq_one_iff p h7ne).mp h1))
    · intro hsq
      refine (legendreSym.eq_one_iff p h7mne).mp ?_
      rw [hmul, hn1, one_mul]
      exact (legendreSym.eq_one_iff p h7ne).mpr (hbridge.mpr (hq7.mpr hsq))
  · have hn1 : legendreSym p (-1 : ℤ) = -1 := by
      refine (legendreSym.eq_neg_one_iff p).mpr ?_
      have hc : ((-1 : ℤ) : ZMod p) = -1 := by push_cast; simp
      rw [hc]
      intro hsq
      have h := (FiniteField.isSquare_neg_one_iff).mp hsq
      rw [hcard] at h
      omega
    have hq7 : IsSquare ((7 : ℕ) : ZMod p) ↔ ¬ IsSquare ((p : ℕ) : ZMod 7) :=
      ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three hp4 (by norm_num) hp7
    have hbridge : IsSquare ((7 : ℤ) : ZMod p) ↔ IsSquare ((7 : ℕ) : ZMod p) := by
      have hc : ((7 : ℤ) : ZMod p) = ((7 : ℕ) : ZMod p) := by push_cast; simp
      rw [hc]
    have hls7 : legendreSym p (7 : ℤ) = 1 ∨ legendreSym p (7 : ℤ) = -1 :=
      sq_eq_one_iff.mp (legendreSym.sq_one p h7ne)
    constructor
    · intro hsq
      have h1 : legendreSym p (-7 : ℤ) = 1 := (legendreSym.eq_one_iff p h7mne).mpr hsq
      rw [hmul, hn1] at h1
      rcases hls7 with hc | hc
      · exfalso
        have hc7 : IsSquare ((7 : ℤ) : ZMod p) := (legendreSym.eq_one_iff p h7ne).mp hc
        have hneg : ¬ IsSquare ((-1 : ℤ) : ZMod p) := (legendreSym.eq_neg_one_iff p).mp hn1
        have hmul2 : ((-7 : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) * ((7 : ℤ) : ZMod p) := by
          push_cast
          ring
        have hdiv : ((-7 : ℤ) : ZMod p) / ((7 : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) :=
          (div_eq_iff h7ne).mpr hmul2
        rw [← hdiv] at hneg
        exact hneg (IsSquare.div hsq hc7)
      · have hnot7 : ¬ IsSquare ((7 : ℤ) : ZMod p) := (legendreSym.eq_neg_one_iff p).mp hc
        by_contra hnb
        have hA : IsSquare ((7 : ℕ) : ZMod p) := hq7.mpr hnb
        exact hnot7 (hbridge.mpr hA)
    · intro hsq
      have hn7 : ¬ IsSquare ((7 : ℤ) : ZMod p) := fun hs => hq7.mp (hbridge.mp hs) hsq
      have hneg : legendreSym p (7 : ℤ) = -1 := (legendreSym.eq_neg_one_iff p).mpr hn7
      refine (legendreSym.eq_one_iff p h7mne).mp ?_
      rw [hmul, hn1, hneg]
      ring

theorem h7mod {p : ℕ} (hp : p.Prime) (hp7 : p ≠ 7) :
    IsSquare ((p : ℕ) : ZMod 7) ↔ (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) := by
  have hne0 : p % 7 ≠ 0 := by
    intro h
    have hd : 7 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime hp).mp hd with h1 | h7eq
    · exact absurd h1 (by norm_num)
    · exact hp7 h7eq.symm
  rw [← ZMod.natCast_mod p 7]
  have hlt : p % 7 < 7 := Nat.mod_lt p (by norm_num)
  interval_cases p % 7
  · exact absurd rfl hne0
  · exact ⟨fun _ => Or.inl rfl, fun _ => Exists.intro (1 : ZMod 7) (by decide)⟩
  · exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => Exists.intro (3 : ZMod 7) (by decide)⟩
  · constructor
    · rintro ⟨y, hy⟩
      have hv := congrArg ZMod.val hy
      rw [ZMod.val_natCast 7, Nat.mod_eq_of_lt hlt, ZMod.val_mul] at hv
      have hyv : y.val < 7 := y.isLt
      interval_cases y.val <;> norm_num at hv
    · intro h; rcases h with h | h | h <;> omega
  · exact ⟨fun _ => Or.inr (Or.inr rfl), fun _ => Exists.intro (2 : ZMod 7) (by decide)⟩
  · constructor
    · rintro ⟨y, hy⟩
      have hv := congrArg ZMod.val hy
      rw [ZMod.val_natCast 7, Nat.mod_eq_of_lt hlt, ZMod.val_mul] at hv
      have hyv : y.val < 7 := y.isLt
      interval_cases y.val <;> norm_num at hv
    · intro h; rcases h with h | h | h <;> omega
  · constructor
    · rintro ⟨y, hy⟩
      have hv := congrArg ZMod.val hy
      rw [ZMod.val_natCast 7, Nat.mod_eq_of_lt hlt, ZMod.val_mul] at hv
      have hyv : y.val < 7 := y.isLt
      interval_cases y.val <;> norm_num at hv
    · intro h; rcases h with h | h | h <;> omega

theorem main (p : ℕ) (hp : p.Prime) :
    OeisA3625.A p ↔ Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) := by
  rcases Nat.Prime.eq_two_or_odd hp with rfl | hodd
  · constructor
    · rintro ⟨_, h⟩; omega
    · intro hirr
      have hz : ((0 : ZMod 2) ^ 2 + 0 + 2 : ZMod 2) = 0 := by decide
      haveI : Fact (2 : ℕ).Prime := ⟨by norm_num⟩
      exact (root_not_irr (0 : ZMod 2) hz hirr).elim
  · have hp2 : p ≠ 2 := by omega
    rcases eq_or_ne p 7 with rfl | hp7
    · constructor
      · rintro ⟨_, h⟩; omega
      · intro hirr
        have hz : ((3 : ZMod 7) ^ 2 + 3 + 2 : ZMod 7) = 0 := by decide
        haveI : Fact (7 : ℕ).Prime := ⟨by norm_num⟩
        exact (root_not_irr (3 : ZMod 7) hz hirr).elim
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [show OeisA3625.A p = (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) from by
        simp [OeisA3625.A, hp]]
      have step1 : (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) ↔
          ¬ (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) := by
        have hne0 : p % 7 ≠ 0 := by
          intro h
          have hd : 7 ∣ p := Nat.dvd_of_mod_eq_zero h
          rcases (Nat.dvd_prime hp).mp hd with h1 | h7eq
          · exact absurd h1 (by norm_num)
          · exact hp7 h7eq.symm
        have hlt : p % 7 < 7 := Nat.mod_lt p (by norm_num : 0 < 7)
        interval_cases h : p % 7
        · exact absurd rfl hne0
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
      rw [step1, ← h7mod hp hp7, ← sq_m7 hp hp2 hp7]
      constructor
      · intro hnsq
        by_contra hred
        exact hnsq ((sq_iff_root hp hp2).mpr (root_of_red hred))
      · intro hirr
        intro hsq
        obtain ⟨x, hx⟩ := (sq_iff_root hp hp2).mp hsq
        exact root_not_irr x hx hirr

theorem swarm_proof (p : ℕ) (hp : p.Prime) :
    OeisA3625.A p ↔ Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) := main p hp
