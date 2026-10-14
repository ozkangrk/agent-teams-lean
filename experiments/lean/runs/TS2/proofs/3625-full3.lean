
import FormalConjectures.OEIS.«3625»

open OeisA3625 Polynomial ZMod legendreSym

namespace A3625Aux

theorem pmod7 (p : Nat) :
    IsSquare ((p : Nat) : ZMod 7) ↔ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by
  have hv : ((p : Nat) : ZMod 7) = ((p % 7 : Nat) : ZMod 7) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val (p : ZMod 7)]
    rw [ZMod.val_natCast]
  rw [hv]
  rcases h : p % 7 with _ | _ | _ | _ | _ | _ | _ <;> decide

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
      rcases Nat.Prime.eq_two_or_odd (Fact.out : p.Prime) with hh | hodd
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
    · have hz : (0 : ZMod p) = (-(7 : ZMod p)) + 7 := by rw [hy2]; ring
      rw [← hz] at h
      exact absurd h (by simp)
  · intro h x hx
    refine h ⟨2 * x + 1, ?_⟩
    have hc : (2 * x + 1) * (2 * x + 1) = 4 * (x ^ 2 + x + 2) + (-7 : ZMod p) := by ring
    rw [hx] at hc
    simp only [mul_zero, zero_add] at hc
    exact hc.symm

theorem sq_neg7_iff (hp2 : p ≠ 2) (hp7 : p ≠ 7) :
    IsSquare (-(7 : ZMod p)) ↔ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by
  have hp2lt : 2 ≤ p := (Fact.out : p.Prime).one_lt
  have hpodd : p % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd (Fact.out : p.Prime) with hh | hodd
    · exact absurd hh hp2
    · exact Nat.odd_iff.mp hodd
  have h7ne : ((7 : ℤ) : ZMod p) ≠ 0 := by
    intro hc
    have hd : ((p : ℤ) ∣ (7 : ℤ)) := (ZMod.intCast_zmod_eq_zero_iff_dvd 7 p).mp hc
    have hd' : p ∣ 7 := by exact_mod_cast hd
    rcases (Nat.dvd_prime (by norm_num)).mp hd' with hh | hh
    · omega
    · exact hp7 hh
  have hpne7 : ((p : Nat) : ZMod 7) ≠ 0 := by
    intro hc
    have hc' : (((p : Nat) : ℤ) : ZMod 7) = 0 := by exact_mod_cast hc
    have hd : ((7 : ℤ) ∣ ((p : Nat) : ℤ)) := (ZMod.intCast_zmod_eq_zero_iff_dvd p 7).mp hc'
    have hd' : 7 ∣ p := by exact_mod_cast hd
    obtain ⟨k, hk⟩ := hd'
    rcases k with 0 | 1 | k + 2
    · omega
    · exact hp7 (by rw [hk]; norm_num)
    · exact Nat.not_prime_mul (by norm_num) (by omega) (hk ▸ (Fact.out : p.Prime))
  have hc : (((-7 : ℤ) : ZMod p)) = (-(7 : ZMod p)) := by push_cast
  rw [← hc, ← legendreSym.eq_one_iff h7ne]
  have e1 : legendreSym p (-(7 : ℤ)) = χ₄ p * legendreSym p ((7 : Nat) : ℤ) :=
    legendreSym.at_neg hp2 7
  rw [e1, χ₄_eq_neg_one_pow hpodd]
  haveI hf7 : Fact (Nat.Prime 7) := by decide
  have hrec := legendreSym.quadratic_reciprocity' (p := p) (q := 7) hp (by norm_num)
  have hL : legendreSym p ((7 : Nat) : ℤ)
      = (-1 : ℤ) ^ (p / 2 * ((7 : Nat) / 2)) * legendreSym 7 ((p : Nat) : ℤ) := by
    rw [hrec, ← mul_assoc]
    have hSS : ((-1 : ℤ) ^ (p / 2 * ((7 : Nat) / 2)))
        * ((-1 : ℤ) ^ (p / 2 * ((7 : Nat) / 2))) = 1 := by
      rw [← pow_add,
        show p / 2 * ((7 : Nat) / 2) + p / 2 * ((7 : Nat) / 2) = 2 * (p / 2 * ((7 : Nat) / 2)) from by omega,
        pow_mul, neg_one_sq, one_pow]
    rw [hSS, one_mul]
  have hsign : ((-1 : ℤ) ^ (p / 2)) * ((-1 : ℤ) ^ (p / 2 * ((7 : Nat) / 2))) = 1 := by
    rw [← pow_add,
      show p / 2 + p / 2 * ((7 : Nat) / 2) = 2 * (p - 1) from by omega,
      pow_mul, neg_one_sq, one_pow]
  rw [hL, ← mul_assoc, hsign, one_mul]
  rw [← legendreSym.eq_one_iff' hpne7, pmod7]

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
    · have hAAA : OeisA3625.A p ↔ (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) := Iff.rfl
      rw [hAAA, irred_iff_noroot, noroot_iff_nonsq hp2,
        not_congr (sq_neg7_iff hp2 h7)]
      constructor <;> intro h <;> omega
