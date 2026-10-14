
import FormalConjectures.OEIS.«3625»

open OeisA3625 Polynomial ZMod legendreSym

namespace A3625Aux

theorem pmod7 (p : Nat) (h0 : p % 7 ≠ 0) :
    IsSquare ((p : Nat) : ZMod 7) ↔ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by
  have hv : ((p : Nat) : ZMod 7) = ((p % 7 : Nat) : ZMod 7) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val (p : ZMod 7)]
    rw [ZMod.val_natCast]
  rw [hv]
  have hlt : p % 7 < 7 := Nat.mod_lt p (by norm_num)
  interval_cases p % 7 <;> first | omega | decide

variable {p : Nat} [Fact p.Prime]

lemma degF : (X ^ 2 + X + 2 : (ZMod p)[X]).natDegree = 2 := by
  have hlt : (X + C (2 : ZMod p) : (ZMod p)[X]).natDegree < (X ^ 2 : (ZMod p)[X]).natDegree := by
    rw [natDegree_X_add_C, natDegree_X_pow]
    norm_num
  rw [add_assoc, show X + 2 = X + C (2 : ZMod p) from rfl,
      natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_X_pow]

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
      exact h x (by simpa using hx)

theorem noroot_iff_nonsq (hp2 : p ≠ 2) :
    ((x : ZMod p) -> x ^ 2 + x + 2 ≠ 0) ↔ ¬ IsSquare (-(7 : ZMod p)) := by
  constructor
  · intro h ⟨y, hy⟩
    refine h ((2 : ZMod p)⁻¹ * (y - 1)) ?_
    have hy2 : y ^ 2 = -(7 : ZMod p) := by rw [pow_two]; exact hy.symm
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro hc
      have hc' : (((2 : ℤ) : ZMod p)) = 0 := by exact_mod_cast hc
      have hd : ((p : ℤ) ∣ (2 : ℤ)) := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp hc'
      have hd' : p ∣ 2 := by exact_mod_cast hd
      rcases (Nat.dvd_prime (by norm_num)).mp hd' with hh | hh
      · exact (Fact.out : p.Prime).ne_one hh
      · exact hp2 hh
    have hz : 2 * ((2 : ZMod p)⁻¹ * (y - 1)) = y - 1 := by
      rw [← mul_assoc, mul_inv_cancel₀ h2ne, one_mul]
    have h4 : (4 : ZMod p) ≠ 0 := by
      intro hc
      have hc' : (((4 : ℤ) : ZMod p)) = 0 := by exact_mod_cast hc
      have hd : ((p : ℤ) ∣ (4 : ℤ)) := (ZMod.intCast_zmod_eq_zero_iff_dvd 4 p).mp hc'
      have hd' : p ∣ 4 := by exact_mod_cast hd
      have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hd'
      rcases Nat.Prime.eq_two_or_odd (Fact.out : p.Prime) with hh | hpodd
      · exact hp2 hh
      · have hp2lt : 2 ≤ p := (Fact.out : p.Prime).one_lt
        have hp3 : p = 3 := by omega
        rw [hp3] at hd'
        norm_num at hd'
    have hexp : (4 : ZMod p) * (((2 : ZMod p)⁻¹ * (y - 1)) ^ 2 + (2 : ZMod p)⁻¹ * (y - 1) + 2)
        = (2 * ((2 : ZMod p)⁻¹ * (y - 1))) ^ 2 + 2 * (2 * ((2 : ZMod p)⁻¹ * (y - 1))) + 8 := by ring
    have hexp2 : (y - 1) ^ 2 + 2 * (y - 1) + 8 = y ^ 2 + 7 := by ring
    have hzero : (4 : ZMod p) * (((2 : ZMod p)⁻¹ * (y - 1)) ^ 2 + (2 : ZMod p)⁻¹ * (y - 1) + 2) = 0 := by
      rw [hexp, hz, hexp2, hy2]; ring
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h h4
    · exact h
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
    rcases Nat.Prime.eq_two_or_odd (Fact.out : p.Prime) with hh | hpodd
    · exact absurd hh hp2
    · exact hpodd
  have h7ne : ((7 : ℤ) : ZMod p) ≠ 0 := by
    intro hc
    have hd : ((p : ℤ) ∣ (7 : ℤ)) := (ZMod.intCast_zmod_eq_zero_iff_dvd 7 p).mp hc
    have hd' : p ∣ 7 := by exact_mod_cast hd
    rcases (Nat.dvd_prime (by norm_num)).mp hd' with hh | hh
    · omega
    · exact hp7 hh
  have h7ndvd : ¬ (7 ∣ p) := by
    intro hd'
    obtain ⟨k, hk⟩ := hd'
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · rcases Nat.lt_two_iff.mp hk2 with rfl | rfl
      · omega
      · exact hp7 (by rw [hk]; norm_num)
    · exact absurd (hk ▸ (Fact.out : p.Prime))
        (Nat.not_prime_mul (by norm_num) (by omega))
  have hpne7 : ((p : Nat) : ZMod 7) ≠ 0 := by
    intro hc
    have hc' : (((p : Nat) : ℤ) : ZMod 7) = 0 := by exact_mod_cast hc
    exact h7ndvd (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd p 7).mp hc')
  have hmod0 : p % 7 ≠ 0 := fun hh => h7ndvd ((Nat.dvd_iff_mod_eq_zero).mpr hh)
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
  rw [← legendreSym.eq_one_iff' hpne7, pmod7 p hmod0]

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
      have he : eval 0 (X ^ 2 + X + 2 : (ZMod 2)[X]) = (0 : ZMod 2) ^ 2 + 0 + 2 := by simp
      have hr : (X ^ 2 + X + 2 : (ZMod 2)[X]).IsRoot 0 := by
        show eval 0 (X ^ 2 + X + 2 : (ZMod 2)[X]) = 0
        rw [he]; decide
      exact hirr.not_isRoot_of_natDegree_ne_one (by rw [degF]; norm_num) hr
  · by_cases h7 : p = 7
    · subst h7
      refine iff_of_false ?_ ?_
      · rintro ⟨-, h⟩
        rcases h with h | h | h <;> norm_num at h
      · intro hirr
        have he : eval 3 (X ^ 2 + X + 2 : (ZMod 7)[X]) = (3 : ZMod 7) ^ 2 + 3 + 2 := by simp
        have hr : (X ^ 2 + X + 2 : (ZMod 7)[X]).IsRoot 3 := by
          show eval 3 (X ^ 2 + X + 2 : (ZMod 7)[X]) = 0
          rw [he]; decide
        exact hirr.not_isRoot_of_natDegree_ne_one (by rw [degF]; norm_num) hr
    · have hAAA : OeisA3625.A p ↔ (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) := Iff.rfl
      rw [hAAA, irred_iff_noroot, noroot_iff_nonsq hp2,
        not_congr (sq_neg7_iff hp2 h7)]
      constructor <;> intro h <;> omega
