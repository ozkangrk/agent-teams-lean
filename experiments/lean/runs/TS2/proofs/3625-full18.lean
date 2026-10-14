
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
    rcases k with _ | m
    · omega
    · rcases m with _ | n
      · exact hp7 (by omega)
      · have hp' : Nat.Prime (7 * (n + 1 + 1)) := hk ▸ (Fact.out : p.Prime)
        exact Nat.not_prime_mul (by norm_num) (by omega) hp'
  have hpne7 : ((p : Nat) : ZMod 7) ≠ 0 := by
    intro hc
    have hc' : (((p : Nat) : ℤ) : ZMod 7) = 0 := by exact_mod_cast hc
    exact h7ndvd (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd p 7).mp hc')
  have hmod0 : p % 7 ≠ 0 := fun hh => h7ndvd ((Nat.dvd_iff_mod_eq_zero).mpr hh)
  have h7ne2 : (((-7 : ℤ)) : ZMod p) ≠ 0 := by
    intro hc2
    have hd : ((p : ℤ) ∣ (-7 : ℤ)) := (ZMod.intCast_zmod_eq_zero_iff_dvd (-7) p).mp hc2
    have hd7 : ((p : ℤ) ∣ (7 : ℤ)) := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨-k, by linarith [hk]⟩
    have hd' : p ∣ 7 := by exact_mod_cast hd7
    rcases (Nat.dvd_prime (by norm_num)).mp hd' with hh | hh
    · exact (Fact.out : p.Prime).ne_one hh
    · exact hp7 hh
  have hc : (((-7 : ℤ) : ZMod p)) = (-(7 : ZMod p)) := by push_cast; rfl
  rw [← hc, ← legendreSym.eq_one_iff p h7ne2]
  have e1 : legendreSym p (-(7 : ℤ)) = χ₄ p * legendreSym p ((7 : Nat) : ℤ) :=
    legendreSym.at_neg hp2 7
  rw [e1, χ₄_eq_neg_one_pow hpodd]
  haveI hf7 : Fact (Nat.Prime 7) := by decide
  have hrec := legendreSym.quadratic_reciprocity' (p := p) (q := 7) hp2 (by norm_num)
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
  rw [legendreSym.eq_one_iff' 7 hpne7, pmod7 p hmod0]

end A3625Aux

open A3625Aux in
theorem swarm_proof (p : Nat) (hp : p.Prime) :
    OeisA3625.A p ↔ Irreducible (X ^ 2 + X + 2 : (ZMod p)[X]) := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold OeisA3625.A
  by_cases h2 : p = 2
  · subst h2
    refine iff_of_false ?_ ?_
    · rintro ⟨-, h⟩
      rcases h with h | h | h <;> norm_num at h
    · intro hirr
      have he : eval 0 (X ^ 2 + X + 2 : (ZMod 2)[X]) = (0 : ZMod 2) ^ 2 + 0 + 2 := by simp
      have hr : (X ^ 2 + X + 2 : (ZMod 2)[X]).IsRoot 0 := by
        show eval 0 (X ^ 2 + X + 2 : (ZMod 2)[X]) = 0
        rw [he]
        have h2 : (0 : ZMod 2) ^ 2 + 0 + 2 = ((2 : ℕ) : ZMod 2) := by ring
        rw [h2]
        exact ZMod.natCast_self 2
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
          rw [he]
          have h14 : (3 : ZMod 7) ^ 2 + 3 + 2 = ((14 : ℕ) : ZMod 7) := by ring
          rw [h14]
          have hc14 : ((14 : ℕ) : ZMod 7) = 0 := by
            conv_lhs => rw [← ZMod.natCast_zmod_val ((14 : ℕ) : ZMod 7)]
            rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by norm_num : 14 % 7 < 7), Nat.cast_zero]
          exact hc14
        exact hirr.not_isRoot_of_natDegree_ne_one (by rw [degF]; norm_num) hr
    · have hmod0 : p % 7 ≠ 0 := by
        intro hh
        have hd : 7 ∣ p := (Nat.dvd_iff_mod_eq_zero).mpr hh
        rcases (Nat.dvd_prime (by norm_num : (7 : Nat).Prime)).mp hd with hh2 | hh2
        · exact absurd hh2 (by norm_num)
        · exact h7 hh2.symm
      rw [and_iff_right hp, irred_iff_noroot, noroot_iff_nonsq h2,
        not_congr (sq_neg7_iff h2 h7)]
      constructor
      · rintro (h | h | h) (h2 | h2 | h2) <;> omega
      · intro h
        push_neg at h
        rcases h with ⟨h1, h2', h4⟩
        have hlt : p % 7 < 7 := Nat.mod_lt p (by norm_num)
        omega
