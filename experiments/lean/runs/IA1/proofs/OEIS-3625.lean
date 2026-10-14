import FormalConjectures.OEIS.«3625»

open Polynomial ZMod legendreSym

theorem root_two : (0 : ZMod 2) * 0 + 0 + 2 = 0 := by decide

theorem root_seven : (3 : ZMod 7) * 3 + 3 + 2 = 0 := by decide

theorem swarm_proof (p : ℕ) (hp : p.Prime) :
    OeisA3625.A p ↔ Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) := by
  haveI := Fact.mk hp
  -- squares mod 7
  have hsq7 : ∀ y : ZMod 7, IsSquare y ↔ y.val = 0 ∨ y.val = 1 ∨ y.val = 2 ∨ y.val = 4 := by
    decide
  -- degree of the polynomial
  have hnum : (2 : (ZMod p)[X]) = C (2 : ZMod p) := (Polynomial.C_ofNat 2).symm
  have hdegf : (X ^ 2 + X + 2 : (ZMod p)[X]).degree = 2 := by
    have h2p : (X + 2 : (ZMod p)[X]) = X + C (2 : ZMod p) := by rw [hnum]
    rw [show (X ^ 2 + X + 2 : (ZMod p)[X]) = (X ^ 2 : (ZMod p)[X]) + (X + 2 : (ZMod p)[X]) from by
        ring,
      Polynomial.degree_add_eq_left_of_degree_lt
        (by rw [h2p, Polynomial.degree_X_add_C, Polynomial.degree_X_pow]; norm_num),
      Polynomial.degree_X_pow]
    norm_num
  have hfx : ∀ x : ZMod p, (X ^ 2 + X + 2 : (ZMod p)[X]).eval x = x * x + x + 2 := by
    intro x
    simp only [eval_add, pow_two, eval_mul, eval_X, eval_ofNat]
  -- irreducibility ↔ no root
  have hroot : Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) ↔ ¬ ∃ a : ZMod p, a * a + a + 2 = 0 := by
    constructor
    · intro hirr
      rintro ⟨a, ha⟩
      have hisroot : (X ^ 2 + X + 2 : (ZMod p)[X]).IsRoot a := by
        rw [IsRoot, hfx, ha]
      obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr hisroot
      rcases hirr.isUnit_or_isUnit hg with hu | hu
      · have hu' : (X - C a : (ZMod p)[X]).degree = 0 :=
          Polynomial.isUnit_iff_degree_eq_zero.mp hu
        rw [Polynomial.degree_X_sub_C] at hu'
        exact absurd hu' (by norm_num)
      · have hgn : g ≠ 0 := hu.ne_zero
        have hX0 : (X - C a : (ZMod p)[X]) ≠ 0 := by
          intro h0
          have hx1 : (X - C a : (ZMod p)[X]).degree = 1 := Polynomial.degree_X_sub_C a
          rw [h0, Polynomial.degree_zero] at hx1
          exact absurd hx1 (by simp)
        have hd := Polynomial.degree_mul'
          (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hX0)
            (Polynomial.leadingCoeff_ne_zero.mpr hgn))
        rw [← hg, hdegf, Polynomial.degree_X_sub_C] at hd
        have hu' : g.degree = 0 := Polynomial.isUnit_iff_degree_eq_zero.mp hu
        rw [hu'] at hd
        exact absurd hd (by norm_num)
    · intro hnoroot
      have hf0 : (X ^ 2 + X + 2 : (ZMod p)[X]) ≠ 0 := by
        intro h0
        rw [h0, Polynomial.degree_zero] at hdegf
        exact absurd hdegf (by simp)
      refine ⟨?_, ?_⟩
      · intro hu
        have hu' : (X ^ 2 + X + 2 : (ZMod p)[X]).degree = 0 :=
          Polynomial.isUnit_iff_degree_eq_zero.mp hu
        rw [hdegf] at hu'
        exact absurd hu' (by norm_num)
      · intro A B hAB
        by_contra hcon
        push_neg at hcon
        obtain ⟨hnuA, hnuB⟩ := hcon
        have hA0 : A ≠ 0 := fun h => hf0 (by rw [hAB, h, zero_mul])
        have hB0 : B ≠ 0 := fun h => hf0 (by rw [hAB, h, mul_zero])
        have h2w : (2 : WithBot ℕ) = ((2 : ℕ) : WithBot ℕ) := by norm_num
        have hdAB : A.natDegree + B.natDegree = 2 := by
          have hd := Polynomial.degree_mul'
              (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hA0)
                (Polynomial.leadingCoeff_ne_zero.mpr hB0))
          rw [← hAB, hdegf, h2w, Polynomial.degree_eq_natDegree hA0,
            Polynomial.degree_eq_natDegree hB0, ← Nat.cast_add] at hd
          exact Nat.cast_injective hd.symm
        have hndA0 : A.natDegree ≠ 0 := by
          intro h0
          apply hnuA
          have hdeg0 : A.degree = 0 := by
            rw [Polynomial.degree_eq_natDegree hA0, h0]
            simp
          exact Polynomial.isUnit_iff_degree_eq_zero.mpr hdeg0
        have hndB0 : B.natDegree ≠ 0 := by
          intro h0
          apply hnuB
          have hdeg0 : B.degree = 0 := by
            rw [Polynomial.degree_eq_natDegree hB0, h0]
            simp
          exact Polynomial.isUnit_iff_degree_eq_zero.mpr hdeg0
        have hnA : A.natDegree = 1 := by omega
        have hnA2 : A.natDegree < 2 := by omega
        have hAsum : A = C (A.coeff 0) + C (A.coeff 1) * X := by
          have h := Polynomial.as_sum_range_C_mul_X_pow' (p := A) (n := 2) hnA2
          rw [h]
          simp [Finset.sum_range_succ, Finset.sum_range_one]
        have hc1 : A.coeff 1 ≠ 0 := by
          intro h0
          rw [h0, map_zero, zero_mul, add_zero] at hAsum
          rw [hAsum, Polynomial.natDegree_C] at hnA
          exact absurd hnA (by norm_num)
        have hrootA : A.eval (-(A.coeff 0) * (A.coeff 1)⁻¹) = 0 := by
          have hev :=
            congrArg (fun q : (ZMod p)[X] => q.eval (-(A.coeff 0) * (A.coeff 1)⁻¹)) hAsum
          rw [hev]
          simp only [eval_add, eval_C, eval_mul, eval_X]
          rw [mul_comm (A.coeff 1), mul_assoc, inv_mul_cancel₀ hc1, mul_one]
          ring
        have hfroot :
            (X ^ 2 + X + 2 : (ZMod p)[X]).eval (-(A.coeff 0) * (A.coeff 1)⁻¹) = 0 := by
          rw [hAB, eval_mul, hrootA, zero_mul]
        exact hnoroot ⟨-(A.coeff 0) * (A.coeff 1)⁻¹, by rw [← hfx]; exact hfroot⟩
  -- branch on p
  rcases Nat.Prime.eq_two_or_odd hp with rfl | hpodd
  · rw [OeisA3625.A]
    constructor
    · rintro ⟨_, h | h | h⟩ <;> exact absurd h (by norm_num)
    · exact fun hirr => (hroot.mp hirr ⟨0, root_two⟩).elim
  rcases eq_or_ne p 7 with rfl | hp7
  · rw [OeisA3625.A]
    constructor
    · rintro ⟨_, h | h | h⟩ <;> exact absurd h (by norm_num)
    · exact fun hirr => (hroot.mp hirr ⟨3, root_seven⟩).elim
  -- main case: p odd, p ≠ 7
  haveI : Fact ((7 : ℕ).Prime) := ⟨by decide⟩
  have hp7prime : (7 : ℕ).Prime := by decide
  have hpmod7 : p % 7 ≠ 0 := by
    intro h0
    exact hp7 ((Nat.prime_dvd_prime_iff_eq hp7prime hp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
  have h7Zp' : ((p : ℕ) : ZMod 7) ≠ 0 := by
    intro h
    have hv := ZMod.val_natCast 7 p
    rw [h, ZMod.val_zero] at hv
    exact hpmod7 hv.symm
  have hu2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hv := ZMod.val_natCast p 2
    rw [show ((2 : ℕ) : ZMod p) = (2 : ZMod p) from rfl, h, ZMod.val_zero] at hv
    have := Nat.le_of_dvd (by norm_num : 0 < 2) (Nat.dvd_of_mod_eq_zero hv.symm)
    have := hp.two_le
    omega
  have hz7' : ((-7 : ℤ) : ZMod p) = -(7 : ZMod p) := by push_cast; norm_num
  have hcastneg : ((-1 : ℤ) : ZMod p) = -(1 : ZMod p) := by push_cast; norm_num
  -- roots ↔ squares of -7
  have hsqiff : (∃ a : ZMod p, a * a + a + 2 = 0) ↔ IsSquare (((-7 : ℤ) : ZMod p)) := by
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨2 * a + 1, ?_⟩
      rw [hz7']
      linear_combination (-4) * ha
    · rintro ⟨y, hy⟩
      rw [hz7'] at hy
      refine ⟨y * (2 : ZMod p)⁻¹ - (2 : ZMod p)⁻¹, ?_⟩
      have h2u : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hu2
      have key :
          (2 : ZMod p) * (2 : ZMod p) *
              ((y * (2 : ZMod p)⁻¹ - (2 : ZMod p)⁻¹) * (y * (2 : ZMod p)⁻¹ - (2 : ZMod p)⁻¹) +
                (y * (2 : ZMod p)⁻¹ - (2 : ZMod p)⁻¹) + 2) = 0 := by
        linear_combination
          ((2 * y * y - 4 * y + 2) * (2 : ZMod p)⁻¹ + (y * y - 1)) * h2u - hy
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h (mul_ne_zero hu2 hu2)
      · exact h
  -- Legendre symbol computation
  have hL : legendreSym p (-7 : ℤ) = legendreSym 7 (p : ℤ) := by
    have hsplit : legendreSym p (-7 : ℤ) = legendreSym p (-1 : ℤ) * legendreSym p 7 := by
      rw [show (-7 : ℤ) = (-1 : ℤ) * 7 from by norm_num, legendreSym.mul]
    rw [hsplit]
    have hmod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hmod4 with h4v | h4v
    · have hneg1ne : ((-1 : ℤ) : ZMod p) ≠ 0 := by
        rw [hcastneg]
        norm_num
      have hn1 : legendreSym p (-1 : ℤ) = 1 := by
        rw [eq_one_iff p hneg1ne, hcastneg, ZMod.exists_sq_eq_neg_one_iff]
        omega
      rw [hn1, one_mul]
      exact (quadratic_reciprocity_one_mod_four h4v (by norm_num : (7 : ℕ) ≠ 2)).symm
    · have hn1 : legendreSym p (-1 : ℤ) = -1 := by
        rw [eq_neg_one_iff, hcastneg, ZMod.exists_sq_eq_neg_one_iff]
        omega
      rw [hn1, quadratic_reciprocity_three_mod_four h4v (by decide : (7 : ℕ) % 4 = 3)]
      ring
  -- final assembly
  rw [OeisA3625.A]
  constructor
  · rintro ⟨_, h⟩
    have hnsq : ¬ IsSquare ((p : ℕ) : ZMod 7) := by
      intro hsq
      have hval := (hsq7 _).mp hsq
      rw [ZMod.val_natCast] at hval
      omega
    have hL2 : legendreSym 7 (p : ℤ) = -1 := by
      rw [eq_neg_one_iff']
      exact hnsq
    have hL3 : legendreSym p (-7 : ℤ) = -1 := by rw [hL]; exact hL2
    have hnsqz : ¬ IsSquare (((-7 : ℤ) : ZMod p)) :=
      (eq_neg_one_iff (p := p) (a := (-7 : ℤ))).mp hL3
    exact hroot.mpr (fun hr => hnsqz (hsqiff.mp hr))
  · intro hirr
    have hnoroot := hroot.mp hirr
    refine ⟨hp, ?_⟩
    have hnsqz : ¬ IsSquare (((-7 : ℤ) : ZMod p)) := fun hsq => hnoroot (hsqiff.mpr hsq)
    have hL3 : legendreSym p (-7 : ℤ) = -1 := by
      rw [eq_neg_one_iff]
      exact hnsqz
    have hL2 : legendreSym 7 (p : ℤ) = -1 := by rw [← hL]; exact hL3
    have hnsq7 : ¬ IsSquare ((p : ℕ) : ZMod 7) := by
      rw [← eq_neg_one_iff']
      exact hL2
    have hval := (hsq7 _).not.mp hnsq7
    rw [ZMod.val_natCast] at hval
    push_neg at hval
    omega
