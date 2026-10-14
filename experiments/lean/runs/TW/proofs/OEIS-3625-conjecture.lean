import FormalConjectures.OEIS.«3625»
import Mathlib.Tactic.NormNum.LegendreSymbol

set_option maxHeartbeats 2000000

open OeisA3625 Polynomial

private theorem irr_quad_of_eval_ne_zero {F : Type*} [Field F] {f : F[X]}
    (hdeg : f.natDegree = 2) (hf : f ≠ 0)
    (h : ∀ x : F, f.eval x ≠ 0) : Irreducible f := by
  have hfu : ¬ IsUnit f := by
    intro hu
    have h0 : f.degree = 0 := (Polynomial.isUnit_iff_degree_eq_zero).mp hu
    rw [degree_eq_natDegree hf, hdeg] at h0
    exact absurd h0 (by norm_num)
  by_contra hirr
  obtain ⟨g, k, hg, hk, hgk⟩ :=
    (irreducible_or_factor (p := f) hfu).resolve_left hirr
  have hg0 : g ≠ 0 := fun hc => hf (by rw [hgk, hc, zero_mul])
  have hk0 : k ≠ 0 := fun hc => hf (by rw [hgk, hc, mul_zero])
  have hd : g.natDegree + k.natDegree = 2 := by
    rw [← natDegree_mul hg0 hk0, ← hgk]; exact hdeg
  have hk1 : 1 ≤ k.natDegree := by
    rcases Nat.eq_zero_or_pos k.natDegree with hc | hc
    · exact (hk ((Polynomial.isUnit_iff_degree_eq_zero).mpr
        (show k.degree = 0 by rw [degree_eq_natDegree hk0, hc]; norm_num))).elim
    · exact hc
  have hg1 : g.natDegree = 1 := by
    rcases Nat.eq_zero_or_pos g.natDegree with hc | hc
    · exact (hg ((Polynomial.isUnit_iff_degree_eq_zero).mpr
        (show g.degree = 0 by rw [degree_eq_natDegree hg0, hc]; norm_num))).elim
    · omega
  obtain ⟨x, hx⟩ := Polynomial.exists_root_of_degree_eq_one (by
    rw [degree_eq_natDegree hg0]; exact_mod_cast hg1)
  apply h x
  rw [hgk, eval_mul, hx, zero_mul]

private theorem not_irr_quad_of_eval_eq_zero {F : Type*} [Field F] {f : F[X]}
    (hdeg : f.natDegree = 2) (hf : f ≠ 0) (x : F) (hx : f.eval x = 0) :
    ¬ Irreducible f := by
  intro hirr
  obtain ⟨g, hg⟩ := (Polynomial.dvd_iff_isRoot (p := f) (a := x)).mpr hx
  have hgu : g ≠ 0 := by
    intro hc
    exact hf (by rw [hg, hc, mul_zero])
  rcases hirr.isUnit_or_isUnit hg with hu | hu
  · rw [Polynomial.isUnit_iff_degree_eq_zero] at hu
    rw [degree_X_sub_C] at hu
    exact absurd hu (by norm_num)
  · rw [Polynomial.isUnit_iff_degree_eq_zero] at hu
    have h1 : g.natDegree = 0 := by
      have h2 : g.degree = (g.natDegree : WithBot ℕ) := degree_eq_natDegree hgu
      rw [h2] at hu
      simpa using hu
    have h2 : f.natDegree = (X - C x).natDegree + g.natDegree := by
      rw [← natDegree_mul (Polynomial.X_sub_C_ne_zero x) hgu, ← hg]
    rw [natDegree_X_sub_C, h1, hdeg] at h2
    omega

private theorem root_iff_isSquare {p : ℕ} (hp : p.Prime) (h2 : (2 : ZMod p) ≠ 0) :
    (∃ x : ZMod p, x * x + x + 2 = 0) ↔ ∃ y : ZMod p, y * y = (-7 : ZMod p) := by
  haveI := Fact.mk hp
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨2 * x + 1, ?_⟩
    have key : (2 * x + 1) * (2 * x + 1) + 7 = 4 * (x * x + x + 2) := by ring
    rw [hx] at key
    simp only [mul_zero] at key
    exact eq_neg_of_add_eq_zero_left key
  · rintro ⟨y, hy⟩
    refine ⟨2⁻¹ * (y - 1), ?_⟩
    have h4 : (4 : ZMod p) ≠ 0 := by
      have h42 : (4 : ZMod p) = 2 * 2 := by push_cast; ring
      rw [h42]; exact mul_ne_zero h2 h2
    have key : 4 * (2⁻¹ * (y - 1) * (2⁻¹ * (y - 1)) + 2⁻¹ * (y - 1) + 2) = y * y + 7 := by
      field_simp
      ring
    rw [hy] at key
    have key2 : 4 * (2⁻¹ * (y - 1) * (2⁻¹ * (y - 1)) + 2⁻¹ * (y - 1) + 2) = 0 := by
      rw [key]; ring
    exact (mul_eq_zero.mp key2).resolve_left h4

private theorem jacobi_chain {p : ℕ} (hodd : Odd p) :
    jacobiSym (-(7 : ℤ)) p = jacobiSym ((p % 7 : ℕ) : ℤ) 7 := by
  have h7odd : Odd (7 : ℕ) := by decide
  have hmod2 : p % 2 = 1 := (Nat.odd_iff.mp hodd)
  have hχ : ZMod.χ₄ p * ZMod.χ₄ p = 1 := by
    have h1 : ZMod.χ₄ p = (-1) ^ (p / 2) := ZMod.χ₄_eq_neg_one_pow hmod2
    rw [h1, ← pow_add, ← Nat.two_mul, pow_mul, neg_one_sq, one_pow]
  have hp41 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hq7 : qrSign p 7 = ZMod.χ₄ p := by
    rw [qrSign]
    rcases hp41 with hc | hc
    · rw [ZMod.χ₄_nat_one_mod_four hc, jacobiSym.one_left]
    · rw [ZMod.χ₄_nat_three_mod_four hc, jacobiSym.at_neg_one h7odd]
      rfl
  have hrec : jacobiSym (7 : ℤ) p = qrSign p 7 * jacobiSym (p : ℤ) 7 :=
    jacobiSym.quadratic_reciprocity' h7odd hodd
  rw [jacobiSym.neg (7 : ℤ) hodd, hrec, hq7, ← mul_assoc, hχ, one_mul,
    jacobiSym.mod_left]
  have hmod : ((p : ℤ) % ((7 : ℕ) : ℤ)) = ((p % 7 : ℕ) : ℤ) := by omega
  rw [hmod]


private lemma quad_natDegree {p : ℕ} (hp : p.Prime) :
    (X ^ 2 + X + 2 : (ZMod p)[X]).natDegree = 2 := by
  haveI := Fact.mk hp
  have hC2 : (2 : (ZMod p)[X]) = C (2 : ZMod p) := rfl
  have h1 : (X ^ 2 + X + 2 : (ZMod p)[X]) = X ^ 2 + (X + C (2 : ZMod p)) := by
    rw [← add_assoc, hC2]
  have hlt : (X + C (2 : ZMod p)).degree < (X ^ 2 : (ZMod p)[X]).degree := by
    rw [degree_X_add_C, degree_X_pow]
    exact_mod_cast one_lt_two
  rw [h1, natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hlt), natDegree_X_pow]

private lemma quad_ne_zero {p : ℕ} (hp : p.Prime) :
    (X ^ 2 + X + 2 : (ZMod p)[X]) ≠ 0 := by
  intro hc
  have h := quad_natDegree hp
  rw [hc] at h
  simp at h

private lemma quad_eval {p : ℕ} (x : ZMod p) :
    (X ^ 2 + X + 2 : (ZMod p)[X]).eval x = x * x + x + 2 := by
  have hC2 : (2 : (ZMod p)[X]) = C (2 : ZMod p) := rfl
  have h1 : ((X ^ 2 : (ZMod p)[X]).eval x) = x * x := by
    rw [Polynomial.eval_pow, Polynomial.eval_X, pow_two]
  have h2 : (X ^ 2 + X + 2 : (ZMod p)[X]).eval x
      = ((X ^ 2 : (ZMod p)[X]).eval x) + ((X : (ZMod p)[X]).eval x) + ((2 : (ZMod p)[X]).eval x) := by
    rw [← Polynomial.eval_add, ← Polynomial.eval_add]
  rw [h2, h1, Polynomial.eval_X]
  have h3 : ((2 : (ZMod p)[X]).eval x) = 2 := by rw [hC2, Polynomial.eval_C]
  rw [h3]

private lemma zmod_two_ne_zero {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro hc
  have hdvd : q ∣ 2 := (CharP.cast_eq_zero_iff (ZMod q) q 2).mp hc
  have h2le : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hq1 : q ≠ 1 := hq.ne_one
  have hq0 : q ≠ 0 := hq.ne_zero
  omega

private theorem hp_odd {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : Odd q :=
  (Nat.Prime.eq_two_or_odd' hq).resolve_left hq2

private theorem no_root_of_res {q : ℕ} (hq : q.Prime)
    (hc : q % 7 = 3 ∨ q % 7 = 5 ∨ q % 7 = 6) :
    ∀ x : ZMod q, (X ^ 2 + X + 2 : (ZMod q)[X]).eval x ≠ 0 := by
  haveI := Fact.mk hq
  have hq2 : q ≠ 2 := by
    intro hc2
    subst hc2
    rcases hc with h | h | h <;> omega
  have hq7 : q ≠ 7 := by
    intro hc7
    subst hc7
    rcases hc with h | h | h <;> omega
  have hodd : Odd q := hp_odd hq hq2
  have h2nz : (2 : ZMod q) ≠ 0 := zmod_two_ne_zero hq hq2
  have hJ : jacobiSym (-(7 : ℤ)) q = -1 := by
    rw [jacobi_chain hodd]
    rcases hc with h | h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hcast : ((-7 : ℤ) : ZMod q) = (-(7 : ZMod q)) := by push_cast; ring
  have hns : ∀ y : ZMod q, y * y ≠ (-(7 : ZMod q)) := by
    intro y hy
    apply ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp hJ
    refine ⟨y, ?_⟩
    rw [hcast]
    exact hy.symm
  intro x hx
  have hroot : ∃ y : ZMod q, y * y = (-(7 : ZMod q)) :=
    (root_iff_isSquare hq h2nz).mp ⟨x, by rw [← quad_eval]; exact hx⟩
  obtain ⟨y, hy⟩ := hroot
  exact hns y hy

private theorem root_of_nres {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq7 : q ≠ 7)
    (hc : q % 7 = 1 ∨ q % 7 = 2 ∨ q % 7 = 4) :
    ∃ x : ZMod q, (X ^ 2 + X + 2 : (ZMod q)[X]).eval x = 0 := by
  haveI := Fact.mk hq
  have hodd : Odd q := hp_odd hq hq2
  have h2nz : (2 : ZMod q) ≠ 0 := zmod_two_ne_zero hq hq2
  have hJ : jacobiSym (-(7 : ℤ)) q = 1 := by
    rw [jacobi_chain hodd]
    rcases hc with h | h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hcast : ((-7 : ℤ) : ZMod q) = (-(7 : ZMod q)) := by push_cast; ring
  obtain ⟨y, hy⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
  rw [hcast] at hy
  have hroot : ∃ x : ZMod q, x * x + x + 2 = 0 :=
    (root_iff_isSquare hq h2nz).mpr ⟨y, hy.symm⟩
  obtain ⟨x, hx⟩ := hroot
  exact ⟨x, by rw [quad_eval]; exact hx⟩

theorem swarm_proof (p : ℕ) (hp : p.Prime) :
    A p ↔ Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) := by
  haveI := Fact.mk hp
  constructor
  · rintro ⟨-, (hc | hc | hc)⟩
    · exact irr_quad_of_eval_ne_zero (quad_natDegree hp) (quad_ne_zero hp)
        (no_root_of_res hp (Or.inl hc))
    · exact irr_quad_of_eval_ne_zero (quad_natDegree hp) (quad_ne_zero hp)
        (no_root_of_res hp (Or.inr (Or.inl hc)))
    · exact irr_quad_of_eval_ne_zero (quad_natDegree hp) (quad_ne_zero hp)
        (no_root_of_res hp (Or.inr (Or.inr hc)))
  · intro hirr
    refine ⟨hp, ?_⟩
    by_contra hcon
    have hm : p % 7 < 7 := Nat.mod_lt _ (by norm_num)
    have hp0 : 0 < p := hp.pos
    rcases show p % 7 = 0 ∨ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 by omega with
      hc | hc | hc | hc
    · -- p % 7 = 0, so p = 7
      have h7dvd : 7 ∣ p := Nat.dvd_of_mod_eq_zero hc
      rcases (Nat.dvd_prime hp).mp h7dvd with hc1 | hc1
      · omega
      · -- hc1 : 7 = p : root at 3
        have hz : (14 : ZMod p) = 0 := by
          have hd : p ∣ 14 := by rw [← hc1]; norm_num
          exact (CharP.cast_eq_zero_iff (ZMod p) p 14).mpr hd
        have h14 : (3 : ZMod p) * (3 : ZMod p) + 3 + 2 = 14 := by norm_num
        have h1 : (X ^ 2 + X + 2 : (ZMod p)[X]).eval 3 = 0 := by
          rw [quad_eval, h14, hz]
        exact (not_irr_quad_of_eval_eq_zero (quad_natDegree hp) (quad_ne_zero hp) 3 h1) hirr
    · rcases Nat.Prime.eq_two_or_odd' hp with hc2 | hodd
      · -- p = 2 : root at 0
        have hz : (2 : ZMod p) = 0 := by
          have hd : p ∣ 2 := by rw [← hc2]
          exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mpr hd
        have h2 : (0 : ZMod p) * (0 : ZMod p) + 0 + 2 = 2 := by norm_num
        have h1 : (X ^ 2 + X + 2 : (ZMod p)[X]).eval 0 = 0 := by
          rw [quad_eval, h2, hz]
        exact (not_irr_quad_of_eval_eq_zero (quad_natDegree hp) (quad_ne_zero hp) 0 h1) hirr
      · obtain ⟨k, hk⟩ := hodd
        have hne2 : p ≠ 2 := by omega
        have hne7 : p ≠ 7 := by omega
        obtain ⟨x, hx⟩ := root_of_nres hp hne2 hne7 (Or.inl hc)
        exact (not_irr_quad_of_eval_eq_zero (quad_natDegree hp) (quad_ne_zero hp) x hx) hirr
    · rcases Nat.Prime.eq_two_or_odd' hp with hc2 | hodd
      · have hz : (2 : ZMod p) = 0 := by
          have hd : p ∣ 2 := by rw [← hc2]
          exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mpr hd
        have h2 : (0 : ZMod p) * (0 : ZMod p) + 0 + 2 = 2 := by norm_num
        have h1 : (X ^ 2 + X + 2 : (ZMod p)[X]).eval 0 = 0 := by
          rw [quad_eval, h2, hz]
        exact (not_irr_quad_of_eval_eq_zero (quad_natDegree hp) (quad_ne_zero hp) 0 h1) hirr
      · obtain ⟨k, hk⟩ := hodd
        have hne2 : p ≠ 2 := by omega
        have hne7 : p ≠ 7 := by omega
        obtain ⟨x, hx⟩ := root_of_nres hp hne2 hne7 (Or.inr (Or.inl hc))
        exact (not_irr_quad_of_eval_eq_zero (quad_natDegree hp) (quad_ne_zero hp) x hx) hirr
    · rcases Nat.Prime.eq_two_or_odd' hp with hc2 | hodd
      · have hz : (2 : ZMod p) = 0 := by
          have hd : p ∣ 2 := by rw [← hc2]
          exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mpr hd
        have h2 : (0 : ZMod p) * (0 : ZMod p) + 0 + 2 = 2 := by norm_num
        have h1 : (X ^ 2 + X + 2 : (ZMod p)[X]).eval 0 = 0 := by
          rw [quad_eval, h2, hz]
        exact (not_irr_quad_of_eval_eq_zero (quad_natDegree hp) (quad_ne_zero hp) 0 h1) hirr
      · obtain ⟨k, hk⟩ := hodd
        have hne2 : p ≠ 2 := by omega
        have hne7 : p ≠ 7 := by omega
        obtain ⟨x, hx⟩ := root_of_nres hp hne2 hne7 (Or.inr (Or.inr hc))
        exact (not_irr_quad_of_eval_eq_zero (quad_natDegree hp) (quad_ne_zero hp) x hx) hirr
