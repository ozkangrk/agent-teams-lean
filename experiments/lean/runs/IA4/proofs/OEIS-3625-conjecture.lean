import FormalConjectures.OEIS.«3625»

open OeisA3625 Polynomial
open scoped legendreSym

theorem quad_deg {F : Type*} [Field F] :
    (X ^ 2 + X + 2 : F[X]).natDegree = 2 := by
  have hc2 : (X ^ 2 + X + 2 : F[X]).coeff 2 = 1 := by
    simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  have hge : 2 ≤ (X ^ 2 + X + 2 : F[X]).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hc2]; exact one_ne_zero)
  have hle : (X ^ 2 + X + 2 : F[X]).natDegree ≤ 2 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hN2 : M + 1 ≠ 2 := by omega
    have hN1 : 1 ≠ M + 1 := by omega
    simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X, hN2, hN1]
    omega
  omega

theorem eval0_zmod2 : (X ^ 2 + X + 2 : (ZMod 2)[X]).eval 0 = 0 := by
  rw [show ((X ^ 2 + X + 2 : (ZMod 2)[X]).eval 0) = (0 : ZMod 2) ^ 2 + (0 : ZMod 2) + (2 : ZMod 2) from by
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X],
    show ((2 : ZMod 2)) = 0 from by decide]
  ring

theorem eval3_zmod7 : (X ^ 2 + X + 2 : (ZMod 7)[X]).eval 3 = 0 := by
  rw [show ((X ^ 2 + X + 2 : (ZMod 7)[X]).eval 3) = (3 : ZMod 7) ^ 2 + (3 : ZMod 7) + (2 : ZMod 7) from by
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X],
    show ((3 : ZMod 7)) ^ 2 + (3 : ZMod 7) + (2 : ZMod 7) = (14 : ZMod 7) from by ring,
    show ((14 : ZMod 7)) = 0 from by decide]

theorem sq2_zmod7 : ((2 : ℕ) : ZMod 7) = (3 : ZMod 7) * (3 : ZMod 7) := by decide
theorem sq4_zmod7 : ((4 : ℕ) : ZMod 7) = (2 : ZMod 7) * (2 : ZMod 7) := by decide
theorem ne3_zmod7 : ((3 : ℕ) : ZMod 7) ≠ 0 := by decide
theorem ne5_zmod7 : ((5 : ℕ) : ZMod 7) ≠ 0 := by decide
theorem ne6_zmod7 : ((6 : ℕ) : ZMod 7) ≠ 0 := by decide
theorem pow3_zmod7 : ¬ (((3 : ℕ) : ZMod 7) ^ (7 / 2) = 1) := by decide
theorem pow5_zmod7 : ¬ (((5 : ℕ) : ZMod 7) ^ (7 / 2) = 1) := by decide
theorem pow6_zmod7 : ¬ (((6 : ℕ) : ZMod 7) ^ (7 / 2) = 1) := by decide

theorem quad_ne {F : Type*} [Field F] : (X ^ 2 + X + 2 : F[X]) ≠ 0 := by
  intro h
  have hc2 : (X ^ 2 + X + 2 : F[X]).coeff 2 = 1 := by
    simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  rw [h] at hc2
  simp at hc2

theorem quad_irr {F : Type*} [Field F] {g : F[X]} (hdeg : g.natDegree = 2)
    (h0 : g ≠ 0) : Irreducible g ↔ ∀ x, ¬ g.eval x = 0 := by
  constructor
  · intro hirr x hx
    obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot).2 hx
    have hd1 : (X - C x).degree = 1 := Polynomial.degree_X_sub_C x
    rcases hirr.isUnit_or_isUnit hq with hu | hu
    · rw [Polynomial.isUnit_iff_degree_eq_zero] at hu
      rw [hd1] at hu; exact absurd hu (by decide)
    · rw [Polynomial.isUnit_iff_degree_eq_zero] at hu
      have hxne : (X - C x) ≠ 0 := by
        intro h; rw [h] at hd1; exact absurd hd1 (by simp)
      have hqne : q ≠ 0 := by
        intro hq0; rw [hq0, mul_zero] at hq; rw [hq] at h0; exact h0 rfl
      have hnd : (X - C x).natDegree + q.natDegree = 2 := by
        rw [← Polynomial.natDegree_mul (p := X - C x) (q := q) hxne hqne, ← hq, hdeg]
      have hqdeg : q.degree = 1 := by
        have hxnn : (X - C x).natDegree = 1 := natDegree_X_sub_C x
        have hqn : q.natDegree = 1 := by omega
        rw [Polynomial.degree_eq_natDegree hqne, hqn]; norm_num
      rw [hqdeg] at hu; exact absurd hu (by decide)
  · intro hroot
    by_contra hirr
    rw [irreducible_iff, not_and_or] at hirr
    rcases hirr with hu | hu
    · rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree h0, hdeg] at hu
      exact absurd hu (by decide)
    · push_neg at hu
      obtain ⟨a, b, hab, hna, hnb⟩ := hu
      have hane : a ≠ 0 := by
        intro ha; rw [ha, zero_mul] at hab; rw [hab] at h0; exact h0 rfl
      have hbne : b ≠ 0 := by
        intro hb; rw [hb, mul_zero] at hab; rw [hab] at h0; exact h0 rfl
      have hnd2 : a.natDegree + b.natDegree = 2 := by
        rw [← Polynomial.natDegree_mul (p := a) (q := b) hane hbne, ← hab, hdeg]
      have ha0 : a.natDegree ≠ 0 := by
        intro h0a
        exact hna (Polynomial.isUnit_iff_degree_eq_zero.mpr (by
          rw [Polynomial.degree_eq_natDegree hane, h0a]; rfl))
      have hb0 : b.natDegree ≠ 0 := by
        intro h0b
        exact hnb (Polynomial.isUnit_iff_degree_eq_zero.mpr (by
          rw [Polynomial.degree_eq_natDegree hbne, h0b]; rfl))
      have hda1 : a.degree = 1 := by
        have : a.natDegree = 1 := by omega
        rw [Polynomial.degree_eq_natDegree hane, this]; norm_num
      have hdb1 : b.degree = 1 := by
        have : b.natDegree = 1 := by omega
        rw [Polynomial.degree_eq_natDegree hbne, this]; norm_num
      obtain ⟨x, hx⟩ := Polynomial.exists_root_of_degree_eq_one hda1
      have hgx : g.eval x = 0 := by
        rw [hab, Polynomial.eval_mul, hx, zero_mul]
      exact hroot x hgx

theorem swarm_proof (p : ℕ) (hp : p.Prime) :
    A p ↔ Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (7 : ℕ).Prime := ⟨by decide⟩
  unfold A
  rcases Nat.Prime.eq_two_or_odd hp with rfl | hpodd
  · -- p = 2 : f has root 0, so reducible; A 2 is false since 2 % 7 = 2
    constructor
    · intro ⟨_, hc⟩; rcases hc with hc | hc | hc <;> norm_num at hc
    · intro hirr
      exact absurd eval0_zmod2 ((quad_irr quad_deg quad_ne).1 hirr 0)
  · -- odd p
    by_cases hp7 : p = 7
    · subst hp7
      constructor
      · intro ⟨_, hc⟩; rcases hc with hc | hc | hc <;> norm_num at hc
      · intro hirr
        exact absurd eval3_zmod7 ((quad_irr quad_deg quad_ne).1 hirr 3)
    · -- main case: odd prime, p ≠ 7
      have hp2 : p ≠ 2 := by omega
      have hne7 : ((7 : ℤ) : ZMod p) ≠ 0 := by
        intro hd
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
        rcases Nat.Prime.eq_one_or_self_of_dvd (by decide : (7 : ℕ).Prime) p
            (Int.natCast_dvd_natCast.mp hd) with h | h
        · exact hp.ne_one h
        · exact hp7 h
      have hne7' : ((p : ℤ) : ZMod 7) ≠ 0 := by
        intro hd
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
        rcases Nat.Prime.eq_one_or_self_of_dvd hp 7
            (Int.natCast_dvd_natCast.mp hd) with h | h
        · exact absurd h (by decide)
        · exact hp7 h.symm
      have hrootform : ∀ r : ZMod p, (X ^ 2 + X + 2 : (ZMod p)[X]).eval r = r ^ 2 + r + 2 :=
        fun r => by simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
      have hkey : ¬ IsSquare ((-7 : ℤ) : ZMod p) ↔
          ∀ r : ZMod p, (X ^ 2 + X + 2 : (ZMod p)[X]).eval r ≠ 0 := by
        constructor
        · intro hns r
          rw [hrootform]
          intro hr
          refine hns ⟨2 * r + 1, ?_⟩
          push_cast
          linear_combination (-4) * hr
        · intro hnr hs
          obtain ⟨y, hy⟩ := hs
          push_cast at hy
          have hy2 : y * y = (-7 : ZMod p) := hy.symm
          have hu : (2 : ZMod p) ≠ 0 := by
            intro hd
            have hd' : ((2 : ℤ) : ZMod p) = 0 := by push_cast; exact hd
            rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hd'
            have hle := Nat.le_of_dvd (by omega : 0 < 2)
              (Int.natCast_dvd_natCast.mp hd')
            exact absurd (show p = 1 by omega) hp.ne_one
          refine hnr ((y - 1) * 2⁻¹) ?_
          rw [hrootform]
          have hu2 : (2 : ZMod p) * 2⁻¹ = 1 := by field_simp
          have h4eq : (4 : ZMod p) * (((y - 1) * 2⁻¹) ^ 2 + (y - 1) * 2⁻¹ + (2 : ZMod p)) = 0 := by
            linear_combination hy2 + ((2 * 2⁻¹ + 1) * (y - 1) ^ 2 + 2 * (y - 1)) * hu2
          have h4ne : (4 : ZMod p) ≠ 0 := by
            intro h4'
            have h22 : (2 : ZMod p) * 2 = 0 := by
              rw [show (2 : ZMod p) * 2 = 4 by ring, h4']
            rcases mul_eq_zero.mp h22 with h | h
            · exact hu h
            · exact hu h
          exact (mul_eq_zero.mp h4eq).resolve_left h4ne
      have hLR : legendreSym p (-7) = legendreSym 7 p := by
        have hn := legendreSym.at_neg (p := p) hp2 (7 : ℤ)
        rw [ZMod.χ₄_eq_neg_one_pow hpodd] at hn
        have hqr' : legendreSym 7 p * legendreSym p 7 = (-1 : ℤ) ^ (p / 2 * 3) := by
          have h0 := legendreSym.quadratic_reciprocity (p := p) (q := 7) hp2 (by decide) hp7
          simpa using h0
        have hA2 : (-1 : ℤ) ^ (p / 2) * (-1 : ℤ) ^ (p / 2) = 1 := by
          rw [← pow_add, show p / 2 + p / 2 = 2 * (p / 2) by omega, pow_mul]
          norm_num
        have hB2 : legendreSym 7 p * legendreSym 7 p = 1 := by
          rcases legendreSym.eq_one_or_neg_one (p := 7) hne7' with h | h <;> rw [h] <;> ring
        have hBne : legendreSym 7 p ≠ 0 := by
          intro hz
          rw [legendreSym.eq_zero_iff] at hz
          exact hne7' hz
        rw [hn]
        apply mul_right_cancel₀ hBne
        calc (-1 : ℤ) ^ (p / 2) * legendreSym p 7 * legendreSym 7 p
            = (-1 : ℤ) ^ (p / 2) * (legendreSym 7 p * legendreSym p 7) := by ring
          _ = (-1 : ℤ) ^ (p / 2) * (-1 : ℤ) ^ (p / 2 * 3) := by rw [hqr']
          _ = (-1 : ℤ) ^ (p / 2) * ((-1 : ℤ) ^ (p / 2)) ^ 3 := by rw [← pow_mul]
          _ = ((-1 : ℤ) ^ (p / 2) * (-1 : ℤ) ^ (p / 2)) * ((-1 : ℤ) ^ (p / 2) * (-1 : ℤ) ^ (p / 2)) := by
              ring
          _ = 1 * 1 := by rw [hA2]
          _ = legendreSym 7 p * legendreSym 7 p := by rw [one_mul]; exact hB2.symm
      have hres : legendreSym 7 p = -1 ↔ (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) := by
        have hmod : legendreSym 7 (p : ℤ) = legendreSym 7 ((p % 7 : ℕ)) := by
          rw [legendreSym.mod 7 (p : ℤ), ← Int.natCast_mod]
        rw [hmod]
        have hmodbound : p % 7 < 7 := Nat.mod_lt _ (by omega)
        interval_cases hpm : p % 7
        · simp [legendreSym.at_zero]
        · rw [legendreSym.eq_neg_one_iff']
          have hw : ((1 : ℕ) : ZMod 7) = (1 : ZMod 7) * (1 : ZMod 7) := by
            rw [Nat.cast_one, one_mul]
          have hs : IsSquare ((1 : ℕ) : ZMod 7) := ⟨1, hw⟩
          constructor
          · intro hns; exact absurd hs hns
          · intro hc; rcases hc with hc | hc | hc <;> simp at hc
        · rw [legendreSym.eq_neg_one_iff']
          have hs : IsSquare ((2 : ℕ) : ZMod 7) := ⟨3, sq2_zmod7⟩
          constructor
          · intro hns; exact absurd hs hns
          · intro hc; rcases hc with hc | hc | hc <;> simp at hc
        · rw [legendreSym.eq_neg_one_iff']
          constructor
          · intro _; exact Or.inl rfl
          · intro hns hs
            have hc := (ZMod.euler_criterion (p := 7) ne3_zmod7).1 hs
            exact absurd hc pow3_zmod7
        · rw [legendreSym.eq_neg_one_iff']
          have hs : IsSquare ((4 : ℕ) : ZMod 7) := ⟨2, sq4_zmod7⟩
          constructor
          · intro hns; exact absurd hs hns
          · intro hc; rcases hc with hc | hc | hc <;> simp at hc
        · rw [legendreSym.eq_neg_one_iff']
          constructor
          · intro _; exact Or.inr (Or.inl rfl)
          · intro hns hs
            have hc := (ZMod.euler_criterion (p := 7) ne5_zmod7).1 hs
            exact absurd hc pow5_zmod7
        · rw [legendreSym.eq_neg_one_iff']
          constructor
          · intro _; exact Or.inr (Or.inr rfl)
          · intro hns hs
            have hc := (ZMod.euler_criterion (p := 7) ne6_zmod7).1 hs
            exact absurd hc pow6_zmod7

      constructor
      · intro ⟨_, hc⟩
        have h1 : legendreSym 7 p = -1 := hres.2 hc
        have h2 : legendreSym p (-7) = -1 := by rw [hLR]; exact h1
        have h3 : ¬ IsSquare ((-7 : ℤ) : ZMod p) := (legendreSym.eq_neg_one_iff p).mp h2
        exact (quad_irr quad_deg quad_ne).2 (hkey.1 h3)
      · intro hirr
        have h4 : ∀ r, (X ^ 2 + X + 2 : (ZMod p)[X]).eval r ≠ 0 :=
          (quad_irr quad_deg quad_ne).1 hirr
        have h3 : ¬ IsSquare ((-7 : ℤ) : ZMod p) := hkey.2 h4
        have h2 : legendreSym p (-7) = -1 := (legendreSym.eq_neg_one_iff p).mpr h3
        have h1 : legendreSym 7 p = -1 := by rw [← hLR]; exact h2
        exact ⟨hp, hres.1 h1⟩
