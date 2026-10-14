import FormalConjectures.OEIS.«3625»

open OeisA3625 Polynomial jacobiSym

theorem swarm_proof (p : ℕ) (hp : p.Prime) :
    A p ↔ Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) := by
  -- small computations FIRST (before any instance hypotheses enter the context)
  have h7p : Nat.Prime 7 := by norm_num
  have eval2 : (X ^ 2 + X + 2 : (ZMod 2)[X]).eval 0 = 0 := by
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, show (2 : (ZMod 2)[X]) = C (2 : ZMod 2) from by rfl]
    decide
  have eval7 : (X ^ 2 + X + 2 : (ZMod 7)[X]).eval 3 = 0 := by
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, show (2 : (ZMod 7)[X]) = C (2 : ZMod 7) from by rfl]
    decide
  have h2z : ((2 : ℕ) : ZMod 7) ≠ 0 := by decide
  have h4z : ((4 : ℕ) : ZMod 7) ≠ 0 := by decide
  have hs2 : IsSquare ((2 : ℕ) : ZMod 7) := ⟨3, by decide⟩
  have hs4 : IsSquare ((4 : ℕ) : ZMod 7) := ⟨2, by decide⟩
  have hns3 : ¬ IsSquare ((3 : ℕ) : ZMod 7) := by decide
  have hns5 : ¬ IsSquare ((5 : ℕ) : ZMod 7) := by decide
  have hns6 : ¬ IsSquare ((6 : ℕ) : ZMod 7) := by decide
  have hJ2 : jacobiSym ((2 : ℕ) : ℤ) 7 = 1 := by
    rw [← @legendreSym.to_jacobiSym 7 ⟨h7p⟩ ((2 : ℕ) : ℤ)]
    exact (@legendreSym.eq_one_iff' 7 ⟨h7p⟩ 2 h2z).mpr hs2
  have hJ4 : jacobiSym ((4 : ℕ) : ℤ) 7 = 1 := by
    rw [← @legendreSym.to_jacobiSym 7 ⟨h7p⟩ ((4 : ℕ) : ℤ)]
    exact (@legendreSym.eq_one_iff' 7 ⟨h7p⟩ 4 h4z).mpr hs4
  have hJ3 : jacobiSym ((3 : ℕ) : ℤ) 7 = -1 := by
    rw [← @legendreSym.to_jacobiSym 7 ⟨h7p⟩ ((3 : ℕ) : ℤ)]
    exact (@legendreSym.eq_neg_one_iff' 7 ⟨h7p⟩ 3).mpr hns3
  have hJ5 : jacobiSym ((5 : ℕ) : ℤ) 7 = -1 := by
    rw [← @legendreSym.to_jacobiSym 7 ⟨h7p⟩ ((5 : ℕ) : ℤ)]
    exact (@legendreSym.eq_neg_one_iff' 7 ⟨h7p⟩ 5).mpr hns5
  have hJ6 : jacobiSym ((6 : ℕ) : ℤ) 7 = -1 := by
    rw [← @legendreSym.to_jacobiSym 7 ⟨h7p⟩ ((6 : ℕ) : ℤ)]
    exact (@legendreSym.eq_neg_one_iff' 7 ⟨h7p⟩ 6).mpr hns6
  haveI := Fact.mk hp
  haveI hp1 : 1 < p := hp.one_lt
  have hn2 : (X ^ 2 + X + 2 : (ZMod p)[X]).natDegree = 2 := by
    rw [show (2 : (ZMod p)[X]) = C (2 : ZMod p) from by rfl]
    have hE : (X ^ 2 + X + C (2 : ZMod p) : (ZMod p)[X]) = X ^ 2 + (X + C (2 : ZMod p)) := by
      ring
    rw [hE, Polynomial.natDegree_add_eq_left_of_degree_lt (by
      rw [Polynomial.degree_X_add_C, Polynomial.degree_X_pow]; norm_num)]
    simp
  -- root -> reducible
  have root_red : ∀ r : ZMod p, (X ^ 2 + X + 2 : (ZMod p)[X]).eval r = 0 →
      ¬ Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) := by
    intro r hr
    obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot (p := X ^ 2 + X + 2) (a := r)).mpr hr
    have hq0 : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hq
      rw [hq] at hn2
      simp at hn2
    have hdX : (X - C r : (ZMod p)[X]).natDegree = 1 := Polynomial.natDegree_X_sub_C r
    have hdq : q.natDegree = 1 := by
      have hdm := Polynomial.natDegree_mul (p := (X - C r : (ZMod p)[X])) (q := q)
        (by intro h0; rw [h0] at hdX; simp at hdX) hq0
      have hsum := congrArg natDegree hq
      rw [hdm, hdX, hn2] at hsum
      omega
    intro hirr
    rcases hirr.isUnit_or_isUnit hq with h | h
    · obtain ⟨a, -, hae⟩ := Polynomial.isUnit_iff.mp h
      have h1 := congrArg Polynomial.natDegree hae
      rw [Polynomial.natDegree_C, hdX] at h1
      simp at h1
    · obtain ⟨a, -, hae⟩ := Polynomial.isUnit_iff.mp h
      have h1 := congrArg Polynomial.natDegree hae
      rw [Polynomial.natDegree_C, hdq] at h1
      simp at h1
  -- degree 1 polynomials have roots
  have deg1_root : ∀ a : (ZMod p)[X], a.natDegree = 1 → ∃ x : ZMod p, a.eval x = 0 := by
    intro a ha
    have ha0 : a ≠ 0 := by intro h0; rw [h0] at ha; simp at ha
    have hc1 : a.coeff 1 ≠ 0 := by
      have hl : Polynomial.leadingCoeff a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha0
      rwa [Polynomial.leadingCoeff, ha] at hl
    refine ⟨-(a.coeff 0) / a.coeff 1, ?_⟩
    rw [Polynomial.eval_eq_sum_range, ha, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, pow_zero, mul_one, pow_one]
    field_simp
    ring
  -- no root -> irreducible
  have hnroot_irr : (∀ r : ZMod p, (X ^ 2 + X + 2 : (ZMod p)[X]).eval r ≠ 0) →
      Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) := by
    intro hnroot
    refine ⟨?_, ?_⟩
    · intro hU
      obtain ⟨c, -, hce⟩ := Polynomial.isUnit_iff.mp hU
      have h1 := congrArg Polynomial.natDegree hce
      rw [Polynomial.natDegree_C, hn2] at h1
      simp at h1
    · intro a b hab
      by_contra hC
      push_neg at hC
      obtain ⟨hau, hbu⟩ := hC
      have ha0 : a ≠ 0 := fun h => by rw [h, zero_mul] at hab; rw [hab] at hn2; simp at hn2
      have hb0 : b ≠ 0 := fun h => by rw [h, mul_zero] at hab; rw [hab] at hn2; simp at hn2
      have hdm : a.natDegree + b.natDegree = 2 := by
        have hsum := congrArg Polynomial.natDegree hab
        rw [Polynomial.natDegree_mul ha0 hb0, hn2] at hsum
        exact hsum.symm
      have hdnn : ∀ c : (ZMod p)[X], ¬IsUnit c → c ≠ 0 → c.natDegree ≠ 0 := by
        intro c hc hc0 h0
        apply hc
        rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.isUnit_C, isUnit_iff_ne_zero]
        intro hr0
        apply hc0
        rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hr0, Polynomial.C_0]
      have hdna := hdnn a hau ha0
      have hdnb := hdnn b hbu hb0
      have hda : a.natDegree = 1 := by omega
      obtain ⟨x, hx⟩ := deg1_root a hda
      exact hnroot x (by rw [hab, Polynomial.eval_mul, hx, zero_mul])
  rcases Nat.Prime.eq_two_or_odd hp with rfl | hpe
  · refine iff_of_false ?_ ?_
    · intro hA
      obtain ⟨-, h | h | h⟩ := hA <;> omega
    · intro hirr
      exact root_red 0 eval2 hirr
  · by_cases h7 : p = 7
    · subst h7
      refine iff_of_false ?_ ?_
      · intro hA
        obtain ⟨-, h | h | h⟩ := hA <;> omega
      · intro hirr
        exact root_red 3 eval7 hirr
    · -- main case: p odd prime, p ≠ 7
      have hpne7 : p ≠ 7 := h7
      have hOdd : Odd p := ⟨p / 2, by omega⟩
      have hpmod : p % 7 ≠ 0 := by
        intro h
        apply hpne7
        have hdvd : 7 ∣ p := Nat.dvd_of_mod_eq_zero h
        rcases (Nat.dvd_prime hp).mp hdvd with h71 | h7p
        · omega
        · exact h7p.symm
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h
        have hd2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
        rcases (Nat.dvd_prime (by decide : (2 : ℕ).Prime)).mp hd2 with h1 | h2 <;> omega
      have h4ne : (4 : ZMod p) ≠ 0 := by
        intro h
        have h2 : (2 : ZMod p) * (2 : ZMod p) = 0 := by
          have he : (2 : ZMod p) * (2 : ZMod p) = 4 := by ring
          rw [he]; exact h
        rcases mul_eq_zero.mp h2 with h' | h' <;> exact h2ne h'
      -- root ↔ square of -7
      have hroot : (∃ r : ZMod p, (X ^ 2 + X + 2 : (ZMod p)[X]).eval r = 0) ↔
          IsSquare ((-7 : ℤ) : ZMod p) := by
        constructor
        · rintro ⟨r, hr⟩
          simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_C, show (2 : (ZMod p)[X]) = C (2 : ZMod p) from by rfl] at hr
          refine ⟨2 * r + 1, ?_⟩
          have key : ((-7 : ℤ) : ZMod p) = (2 * r + 1) * (2 * r + 1) - 4 * (r ^ 2 + r + 2) := by
            push_cast; ring
          rw [hr, mul_zero, sub_zero] at key
          exact key
        · rintro ⟨y, hy⟩
          refine ⟨(y - 1) * (2 : ZMod p)⁻¹, ?_⟩
          simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_C, show (2 : (ZMod p)[X]) = C (2 : ZMod p) from by rfl]
          have h2x : 2 * ((y - 1) * (2 : ZMod p)⁻¹) = y - 1 := by
            field_simp
          have key : 4 * (((y - 1) * (2 : ZMod p)⁻¹) ^ 2 + (y - 1) * (2 : ZMod p)⁻¹ + 2)
              = (2 * ((y - 1) * (2 : ZMod p)⁻¹) + 1) * (2 * ((y - 1) * (2 : ZMod p)⁻¹) + 1)
                - ((-7 : ℤ) : ZMod p) := by
            push_cast; ring
          rw [h2x, sub_add_cancel] at key
          have key2 : 4 * (((y - 1) * (2 : ZMod p)⁻¹) ^ 2 + (y - 1) * (2 : ZMod p)⁻¹ + 2)
              = 0 := by
            rw [key, ← hy]
            ring
          exact (mul_eq_zero.mp key2).resolve_left h4ne
      -- Jacobi symbol computation
      have hJ1 : jacobiSym (-7 : ℤ) p = jacobiSym ((p % 7 : ℕ) : ℤ) 7 := by
        have hJneg : jacobiSym (-7 : ℤ) p = ZMod.χ₄ p * jacobiSym (7 : ℤ) p :=
          jacobiSym.neg 7 hOdd
        have hQR : jacobiSym ((7 : ℕ) : ℤ) p = (-1 : ℤ) ^ (7 / 2 * (p / 2)) * jacobiSym (p : ℤ) 7 :=
          jacobiSym.quadratic_reciprocity (show Odd 7 by decide) hOdd
        have hbc : jacobiSym ((7 : ℕ) : ℤ) p = jacobiSym (7 : ℤ) p := by push_cast; rfl
        have hchi : ZMod.χ₄ p = (-1 : ℤ) ^ (p / 2) := ZMod.χ₄_eq_neg_one_pow hpe
        have hsign : ZMod.χ₄ p * (-1 : ℤ) ^ (7 / 2 * (p / 2)) = 1 := by
          rw [hchi]
          have hpe2 : p / 2 + 7 / 2 * (p / 2) = 2 * (2 * (p / 2)) := by omega
          rw [← pow_add, hpe2, pow_mul]
          norm_num
        rw [hJneg, ← hbc, hQR, ← mul_assoc, hsign, one_mul]
        rw [jacobiSym.mod_left]
        push_cast
        rfl
      -- square ↔ residue in {1,2,4}
      have hsq : IsSquare ((-7 : ℤ) : ZMod p) ↔ (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) := by
        constructor
        · intro hSq
          have hres : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 3 ∨ p % 7 = 4 ∨ p % 7 = 5 ∨
              p % 7 = 6 := by omega
          rcases hres with h | h | h | h | h | h
          · omega
          · omega
          · exact absurd hSq ((ZMod.nonsquare_iff_jacobiSym_eq_neg_one).mp
              (by rw [hJ1, h]; exact hJ3))
          · omega
          · exact absurd hSq ((ZMod.nonsquare_iff_jacobiSym_eq_neg_one).mp
              (by rw [hJ1, h]; exact hJ5))
          · exact absurd hSq ((ZMod.nonsquare_iff_jacobiSym_eq_neg_one).mp
              (by rw [hJ1, h]; exact hJ6))
        · rintro (h | h | h)
          · rw [h] at hJ1
            exact ZMod.isSquare_of_jacobiSym_eq_one (hJ1.trans (jacobiSym.one_left 7))
          · rw [h] at hJ1
            exact ZMod.isSquare_of_jacobiSym_eq_one (hJ1.trans hJ2)
          · rw [h] at hJ1
            exact ZMod.isSquare_of_jacobiSym_eq_one (hJ1.trans hJ4)
      -- final assembly
      constructor
      · intro hA
        apply hnroot_irr
        intro r hr
        obtain ⟨-, h | h | h⟩ := hA
        all_goals exact absurd (hsq.mp (hroot.mp ⟨r, hr⟩)) (by omega)
      · intro hirr
        by_contra hA
        have hnroot : ∀ r : ZMod p, (X ^ 2 + X + 2 : (ZMod p)[X]).eval r ≠ 0 := by
          intro r hr
          exact Irreducible.not_isRoot_of_natDegree_ne_one hirr (by rw [hn2]; omega) hr
        have hnsq : ¬ IsSquare ((-7 : ℤ) : ZMod p) := by
          intro hs
          obtain ⟨y, hy⟩ := hs
          obtain ⟨r, hr⟩ := hroot.mpr ⟨y, hy⟩
          exact hnroot r hr
        have hnr : ¬(p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) := fun hc => hnsq (hsq.mpr hc)
        exact hA ⟨hp, by omega⟩
