
import FormalConjectures.OEIS.«3625»

open OeisA3625 Polynomial ZMod legendreSym

namespace A3625Aux

variable {p : Nat} [Fact p.Prime]

lemma degF : (X ^ 2 + X + 2 : (ZMod p)[X]).natDegree = 2 := by
  rw [show (X ^ 2 + X + 2 : (ZMod p)[X]) = (X ^ 2 + C (2 : ZMod p)) + X from by ring]
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow_add_C
  · simp

theorem irred_iff_noroot : Irreducible (X ^ 2 + X + 2 : (ZMod p)[X])
    ↔ (x : ZMod p) -> x ^ 2 + x + 2 ≠ 0 := by
  constructor
  · intro hirr x hx
    exact hirr.not_isRoot_of_natDegree_ne_one (by rw [degF]; norm_num) hx
  · intro h
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · simp [degF]
    · intro x hx
      simpa using h x

theorem root_iff_sq (hp2 : p ≠ 2) :
    (¬ ((x : ZMod p) -> x ^ 2 + x + 2 ≠ 0)) ↔ IsSquare (-(7 : ZMod p)) := by
  rw [not_forall]
  push_neg
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨2 * x + 1, ?_⟩
    have h : (2 * x + 1) ^ 2 = 4 * (x ^ 2 + x + 2) + (-7 : ZMod p) := by ring
    rw [hx] at h
    simpa using h
  · rintro ⟨y, hy⟩
    refine ⟨(y - 1) / 2, ?_⟩
    have h4 : (4 : ZMod p) ≠ 0 := by
      intro hc
      have hd : p ∣ 4 := (ZMod.natCast_zmod_eq_zero_iff_dvd 4).mp hc
      rcases Nat.Prime.eq_two_or_odd hp with h2 | hodd
      · exact hp2 h2
      · have : p ≤ 4 := Nat.le_of_dvd (by norm_num) hd
        have hpe : p % 2 = 1 := by omega
        omega
    have hcalc : (4 : ZMod p) * (((y - 1) / 2) ^ 2 + (y - 1) / 2 + 2) = y ^ 2 + 7 := by
      field_simp
      ring
    rw [hy] at hcalc
    have h0 : y ^ 2 + 7 = (0 : ZMod p) := by rw [hy]; ring
    rw [h0] at hcalc
    rcases mul_eq_zero.mp hcalc with h | h
    · exact absurd h h4
    · exact h
