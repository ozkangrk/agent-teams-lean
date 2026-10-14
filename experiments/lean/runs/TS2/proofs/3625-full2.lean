
import FormalConjectures.OEIS.«3625»

open OeisA3625 Polynomial ZMod legendreSym

namespace A3625Aux

theorem pmod7 (p : Nat) :
    IsSquare ((p : Nat) : ZMod 7) ↔ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by
  have hv : ((p : Nat) : ZMod 7) = ((p % 7 : Nat) : ZMod 7) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val (p : ZMod 7)]
    rw [ZMod.val_natCast]
  rw [hv]
  have hlt : p % 7 < 7 := by omega
  interval_cases p % 7 with h <;> rw [h] <;> decide

variable {p : Nat} [Fact p.Prime]

lemma degF : (X ^ 2 + X + 2 : (ZMod p)[X]).natDegree = 2 := by
  have hsplit : (X ^ 2 + X + 2 : (ZMod p)[X]) = X ^ 2 + (X + C (2 : ZMod p)) := by ring
  rw [hsplit]
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow
  · exact natDegree_X_add_C

theorem irred_iff_noroot : Irreducible (X ^ 2 + X + 2 : (ZMod p)[X])
    ↔ (x : ZMod p) -> x ^ 2 + x + 2 ≠ 0 := by
  constructor
  · intro hirr x hx
    exact hirr.not_isRoot_of_natDegree_ne_one (by rw [degF]; norm_num)
      (by simpa using hx)
  · intro h
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · simp [degF]
    · intro x hx
      exact hx (by simpa using h x)

theorem noroot_iff_nonsq (hp2 : p ≠ 2) :
    ((x : ZMod p) -> x ^ 2 + x + 2 ≠ 0) ↔ ¬ IsSquare (-(7 : ZMod p)) := by
  constructor
  · intro h ⟨y, hy⟩
    refine h ((y - 1) / 2) ?_
    have hy2 : y ^ 2 = -(7 : ZMod p) := by rw [pow_two]; exact hy.symm
    have h4 : (4 : ZMod p) ≠ 0 := by
      intro hc
      have hd : ((p : ℤ) ∣ (4 : ℤ)) := (ZMod.intCast_zmod_eq_zero_iff_dvd 4 p).mp hc
      have hd' : p ∣ 4 := by exact_mod_cast hd
      have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hd'
      rcases Nat.Prime.eq_two_or_odd (Fact.out) with hh | hodd
      · exact hp2 hh
      · have hpodd : p % 2 = 1 := by omega
        have hp3 : p = 3 := by omega
        subst hp3; norm_num at hd'
    have hcalc : (4 : ZMod p) * (((y - 1) / 2) ^ 2 + (y - 1) / 2 + 2) = y ^ 2 + 7 := by
      field_simp
      ring
    rw [hy2] at hcalc
    rcases mul_eq_zero.mp hcalc with h | h
    · exact absurd h h4
    · have : (0:ZMod p) = (-(7:ZMod p)) + 7 := by rw [hy2]; ring
      rw [← this] at h
      exact absurd h (by simp)
  · intro h x hx
    refine h ⟨2 * x + 1, ?_⟩
    have hc : (2 * x + 1) * (2 * x + 1) = 4 * (x ^ 2 + x + 2) + (-7 : ZMod p) := by ring
    rw [hx] at hc
    simp only [mul_zero, zero_add] at hc
    exact hc.symm

end A3625Aux

open A3625Aux in
theorem swarm_proof (p : Nat) (hp : p.Prime) :
    OeisA3625.A p ↔ Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases h2 : p = 2
  · subst h2
    refine iff_of_false ?_ ?_
    · rintro ⟨-, h⟩
      rcases h with h | h | h <;> norm_num at h
    · intro hirr
      exact hirr.not_isRoot_of_natDegree_ne_one (by rw [degF]; norm_num)
        (by simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C]; decide)
  · by_cases h7 : p = 7
    · subst h7
      refine iff_of_false ?_ ?_
      · rintro ⟨-, h⟩
        rcases h with h | h | h <;> norm_num at h
      · intro hirr
        exact hirr.not_isRoot_of_natDegree_ne_one (by rw [degF]; norm_num)
          (by simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C]; decide)
    ·
      sorry
