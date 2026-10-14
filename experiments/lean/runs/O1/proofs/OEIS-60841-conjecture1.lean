import FormalConjectures.OEIS.«60841»
/-! M1: closed form  ((lcmMatrix n).det)⁻¹ = ∏_{k ∈ range n} ((k:ℚ)+1)²/φ(k+1). -/

open Matrix Nat

namespace LcmDet

def addOneEmb : ℕ ↪ ℕ := ⟨(·+1), fun _ _ h => Nat.succ.inj h⟩

/-- `A i d = 1/(i+1)` if `d+1 ∣ i+1`, else `0`. -/
def A (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i d ↦ if (d : ℕ) + 1 ∣ (i : ℕ) + 1 then (1 : ℚ) / ((i : ℕ) + 1) else 0

/-- Diagonal matrix of totients. -/
def Dphi (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal fun d : Fin n ↦ (((d : ℕ) + 1).totient : ℚ)

/-- Sum of totients over divisors of `g` (needs `1 ≤ g ≤ n`), cast to a ring. -/
theorem sum_totient_div {R : Type*} [CommSemiring R] (n g : ℕ) (hg1 : 1 ≤ g) (hg : g ≤ n) :
    ∑ d : Fin n, (if (d : ℕ) + 1 ∣ g then (((d : ℕ) + 1).totient : R) else 0) = ((g : ℕ) : R) := by
  classical
  have hconv : ∑ m ∈ Finset.range n, (if m + 1 ∣ g then ((m + 1).totient : R) else 0)
      = ∑ d : Fin n, (if (d : ℕ) + 1 ∣ g then (((d : ℕ) + 1).totient : R) else 0) :=
    Finset.sum_range _
  rw [← hconv]
  have hmap : ∑ u ∈ Finset.map addOneEmb (Finset.range n), (if u ∣ g then (u.totient : R) else 0)
      = ∑ m ∈ Finset.range n, (if m + 1 ∣ g then ((m + 1).totient : R) else 0) :=
    Finset.sum_map _ _ _
  rw [← hmap]
  have hsub : g.divisors ⊆ Finset.map addOneEmb (Finset.range n) := by
    intro u hu
    rw [Nat.mem_divisors] at hu
    obtain ⟨hdvd, hg0⟩ := hu
    have u1 : 1 ≤ u := Nat.pos_of_dvd_of_pos hdvd hg1
    have hle : u ≤ g := Nat.le_of_dvd (by omega) hdvd
    refine Finset.mem_map.2 ⟨u - 1, Finset.mem_range.2 (by omega), ?_⟩
    show u - 1 + 1 = u
    omega
  have hzero : ∀ u ∈ Finset.map addOneEmb (Finset.range n), u ∉ g.divisors →
      (if u ∣ g then (u.totient : R) else 0) = 0 := by
    intro u _ hu
    by_cases hu' : u ∣ g
    · exact absurd (Nat.mem_divisors.2 ⟨hu', by omega⟩) hu
    · simp [hu']
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_congr rfl fun u hu ↦ if_pos (Nat.mem_divisors.1 hu).1]
  rw [← Nat.cast_sum, Nat.sum_totient]

theorem lcm_eq (n : ℕ) : OeisA60841.lcmMatrix n = A n * Dphi n * (A n)ᵀ := by
  ext i j
  classical
  have hc : ∀ d : Fin n, ((d : ℕ) + 1 ∣ (i : ℕ) + 1 ∧ (d : ℕ) + 1 ∣ (j : ℕ) + 1)
      ↔ (d : ℕ) + 1 ∣ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) :=
    fun d ↦ ⟨fun ⟨ha, hb⟩ ↦ Nat.dvd_gcd ha hb, fun h ↦
      ⟨Nat.dvd_trans h (Nat.gcd_dvd_left _ _), Nat.dvd_trans h (Nat.gcd_dvd_right _ _)⟩⟩
  have hg1 : 1 ≤ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) (by omega)
  have hgcd : Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) ≤ n := by
    have hle : Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) ≤ (i : ℕ) + 1 :=
      Nat.le_of_dvd (show 0 < (i : ℕ) + 1 by omega) (Nat.gcd_dvd_left _ _)
    have hi : (i : ℕ) + 1 ≤ n := by omega
    omega
  have hed : ∀ d : Fin n,
      ((if (d : ℕ) + 1 ∣ (i : ℕ) + 1 then (1 : ℚ) / ((i : ℕ) + 1) else 0) *
        ((d : ℕ) + 1).totient) *
      (if (d : ℕ) + 1 ∣ (j : ℕ) + 1 then (1 : ℚ) / ((j : ℕ) + 1) else 0)
      = (if (d : ℕ) + 1 ∣ (i : ℕ) + 1 ∧ (d : ℕ) + 1 ∣ (j : ℕ) + 1
          then (((d : ℕ) + 1).totient : ℚ) else 0) / (((i : ℕ) + 1) * ((j : ℕ) + 1)) := by
    intro d
    by_cases h1 : (d : ℕ) + 1 ∣ (i : ℕ) + 1 <;> by_cases h2 : (d : ℕ) + 1 ∣ (j : ℕ) + 1 <;>
      simp [h1, h2] <;> field_simp <;> ring
  have h1 : (A n * Dphi n * (A n)ᵀ) i j
      = ∑ d : Fin n, ((if (d : ℕ) + 1 ∣ (i : ℕ) + 1 then (1 : ℚ) / ((i : ℕ) + 1) else 0) *
          ((d : ℕ) + 1).totient) *
        (if (d : ℕ) + 1 ∣ (j : ℕ) + 1 then (1 : ℚ) / ((j : ℕ) + 1) else 0) := by
    have hD : Dphi n = Matrix.diagonal (fun d : Fin n ↦ (((d : ℕ) + 1).totient : ℚ)) := rfl
    rw [mul_apply, hD]
    simp only [Matrix.mul_diagonal, transpose_apply]
    rw [show A n = Matrix.of
      (fun (i d : Fin n) ↦ if (d : ℕ) + 1 ∣ (i : ℕ) + 1 then (1 : ℚ) / ((i : ℕ) + 1) else 0) from rfl]
    simp only [Matrix.of_apply]
  have hsum : ∑ d : Fin n, (if (d : ℕ) + 1 ∣ (i : ℕ) + 1 ∧ (d : ℕ) + 1 ∣ (j : ℕ) + 1
          then (((d : ℕ) + 1).totient : ℚ) else 0)
      = ∑ d : Fin n, (if (d : ℕ) + 1 ∣ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)
          then (((d : ℕ) + 1).totient : ℚ) else 0) :=
    Finset.sum_congr rfl fun d _ ↦ by simp only [hc d]
  rw [h1, Finset.sum_congr rfl (fun d _ ↦ hed d), ← Finset.sum_div, hsum,
    sum_totient_div n (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)) hg1 hgcd]
  have ha1 : (0:ℚ) < (((i : ℕ) : ℚ) + 1) := by positivity
  have hb1 : (0:ℚ) < (((j : ℕ) : ℚ) + 1) := by positivity
  have hl1 : (0:ℚ) < ((Nat.lcm ((i : ℕ) + 1) ((j : ℕ) + 1) : ℕ) : ℚ) :=
    Nat.cast_pos.2 (Nat.lcm_pos (Nat.succ_pos _) (Nat.succ_pos _))
  show (1 : ℚ) / ((Nat.lcm ((i : ℕ) + 1) ((j : ℕ) + 1) : ℕ) : ℚ)
      = ((Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) : ℕ) : ℚ)
        / ((((i : ℕ) : ℚ) + 1) * (((j : ℕ) : ℚ) + 1))
  rw [div_eq_div_iff hl1.ne' (mul_ne_zero ha1.ne' hb1.ne')]
  rw [← Nat.cast_mul, Nat.gcd_mul_lcm, ← Nat.cast_succ (i : ℕ), ← Nat.cast_succ (j : ℕ),
    ← Nat.cast_mul, one_mul]

theorem detA_prod (n : ℕ) : (A n).det = (∏ i : Fin n, (((i : ℕ) : ℚ) + 1))⁻¹ := by
  have htri : (A n).IsLowerTriangular := by
    intro i j hij
    simp only [OrderDual.toDual_lt_toDual] at hij
    by_cases hd : ((j : ℕ) + 1) ∣ ((i : ℕ) + 1)
    · exact absurd (Nat.le_of_dvd (show 0 < (i : ℕ) + 1 by omega) hd) (by omega)
    · show (if ((j : ℕ) + 1) ∣ ((i : ℕ) + 1) then (1 : ℚ) / ((i : ℕ) + 1) else 0) = 0
      rw [if_neg hd]
  rw [Matrix.det_of_isLowerTriangular (A n) htri]
  have hdiag : ∀ i : Fin n, A n i i = (((((i : ℕ) : ℚ) + 1))⁻¹) := by
    intro i
    simp [A]
  rw [Finset.prod_congr rfl (fun i _ ↦ hdiag i), Finset.prod_inv_distrib]

theorem det_closed (n : ℕ) :
    ((OeisA60841.lcmMatrix n).det)⁻¹
      = ∏ k ∈ Finset.range n, (((((k : ℚ) + 1)^2) / ((k + 1).totient : ℚ))) := by
  have hV0 : (∏ i : Fin n, (((i : ℕ) : ℚ) + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ by positivity
  have hP0 : (∏ i : Fin n, (((i : ℕ) + 1).totient : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦
      Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.mp (Nat.totient_pos.2 (by omega)))
  have hdetD : (Dphi n).det = ∏ i : Fin n, (((i : ℕ) + 1).totient : ℚ) := by
    show (Matrix.diagonal (fun d : Fin n ↦ (((d:ℕ)+1).totient:ℚ))).det = _
    rw [Matrix.det_diagonal]
  rw [lcm_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, detA_prod, hdetD]
  rw [Finset.prod_div_distrib]
  have hV2 : ∏ k ∈ Finset.range n, ((((k : ℚ) + 1)^2))
      = (∏ i : Fin n, (((i : ℕ) : ℚ) + 1))^2 := by
    rw [Finset.prod_pow, Finset.prod_range]
  have hP : ∏ k ∈ Finset.range n, ((k + 1).totient : ℚ)
      = ∏ i : Fin n, (((i : ℕ) + 1).totient : ℚ) :=
    Finset.prod_range _
  rw [hV2, hP]
  field_simp

end LcmDet

/-- Bridge: `.den = 1` iff the totient product divides the square product (all in ℕ). -/
theorem den_bridge (n : ℕ) :
    (((OeisA60841.lcmMatrix n).det)⁻¹.den = 1) ↔
    ((∏ k ∈ Finset.range n, (k + 1).totient) ∣ ∏ k ∈ Finset.range n, (k + 1)^2) := by
  rw [LcmDet.det_closed, Finset.prod_div_distrib]
  have hnum : ∏ k ∈ Finset.range n, ((k : ℚ) + 1)^2
      = ((∏ k ∈ Finset.range n, (k + 1)^2 : ℕ) : ℚ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    push_cast
    ring
  have hden : ∏ k ∈ Finset.range n, ((k + 1).totient : ℚ)
      = ((∏ k ∈ Finset.range n, (k + 1).totient : ℕ) : ℚ) := (Nat.cast_prod _ _).symm
  rw [hnum, hden]
  have hcI : ∀ m : ℕ, ((m : ℚ) : ℚ) = ((m : ℤ) : ℚ) := fun m => by push_cast; rfl
  rw [hcI, hcI]
  have hB0 : (0:ℤ) < ↑(∏ k ∈ Finset.range n, (k + 1).totient) := by
    have : ∀ k ∈ Finset.range n, 0 < (k + 1).totient := fun k _ =>
      Nat.totient_pos.2 (Nat.succ_pos k)
    exact_mod_cast Finset.prod_pos this
  rw [Rat.den_div_intCast_eq_one_iff _ _ (ne_of_gt hB0), Int.natCast_dvd_natCast]

/-- Finite classification below 100. -/
theorem classify : ∀ n : ℕ, 1 ≤ n → n < 100 →
    ((∏ k ∈ Finset.range n, (k + 1).totient ∣ ∏ k ∈ Finset.range n, (k + 1)^2) ↔
      ((1 ≤ n ∧ n ≤ 34) ∨ n = 36 ∨ n = 38)) := by
  decide +kernel

namespace BigN

open scoped Nat

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def P : Finset ℕ :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}

def D : ℕ := ∏ p ∈ P, p

def num : ℕ := ∑ p ∈ P, padicValNat 2 (p - 1) * (D / p)

def bnd : ℕ := ∑ p ∈ P, padicValNat 2 (p - 1) * (D / p) * (p - 1)

abbrev S (m : ℕ) : ℕ := ∑ p ∈ Finset.filter (fun q => q ∣ m) P, padicValNat 2 (p - 1)

lemma primesP : ∀ p ∈ P, p.Prime := by decide

lemma threeP : ∀ p ∈ P, 3 ≤ p := by decide

lemma maxP : ∀ p ∈ P, p ≤ 97 := by decide

lemma v2_eq_zero_of_odd {m : ℕ} (h : ¬ 2 ∣ m) : padicValNat 2 m = 0 := by
  by_contra hc
  have hm0 : m ≠ 0 := by intro h0; rw [h0] at h; exact h (by omega)
  have h1 : 1 ≤ padicValNat 2 m := by omega
  have h2 : (2 : ℕ) ^ 1 ∣ 2 ^ padicValNat 2 m := Nat.pow_dvd_pow 2 h1
  have h3 : 2 ^ padicValNat 2 m ∣ m :=
    (Nat.pow_dvd_iff_le_padicValNat (by omega) hm0).mpr (le_refl _)
  exact h (h2.trans h3)

/-- Factor out all powers of a divisor `p ≥ 2` from `t ≥ 1` with `p ∣ t`. -/
lemma exists_pow_mul : ∀ t p : ℕ, 2 ≤ p → 1 ≤ t → p ∣ t →
    ∃ e s, 1 ≤ e ∧ ¬ p ∣ s ∧ t = p ^ e * s := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro p hp2 ht hdvd
    obtain ⟨t', hteq⟩ := hdvd
    rw [hteq] at ht ⊢
    have ht0 : t' ≠ 0 := by rintro rfl; simp at ht
    have ht' : 1 ≤ t' := by omega
    by_cases hdvd' : p ∣ t'
    · have hlt : t' < t := by
        have h1 : t' + 1 ≤ 2 * t' := by omega
        have h2 : 2 * t' ≤ p * t' := Nat.mul_le_mul_right t' (by omega)
        rw [hteq]
        omega
      obtain ⟨e, s, he, hs, hsteq⟩ := ih t' hlt p hp2 ht' hdvd'
      refine ⟨e + 1, s, by omega, hs, ?_⟩
      rw [hsteq, pow_succ]
      ring
    · exact ⟨1, t', by omega, hdvd', by ring⟩

/-- For odd `m`, the odd-prime 2-adic contributions to `φ m` cover `S m`. -/
lemma S_le_v2_phi_odd : ∀ m : ℕ, ¬ 2 ∣ m → S m ≤ padicValNat 2 m.totient := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hodd
    by_cases hS : (Finset.filter (fun q => q ∣ m) P).Nonempty
    · obtain ⟨p, hp⟩ := hS
      obtain ⟨hpP, hpdvd⟩ := Finset.mem_filter.1 hp
      have hp3 : 3 ≤ p := threeP p hpP
      have hm1 : 1 ≤ m := by
        have : m ≠ 0 := by intro h0; rw [h0] at hodd; omega
        omega
      obtain ⟨e, s, he, hps, hmeq⟩ := exists_pow_mul m p (by omega) hm1 hpdvd
      have hpcop : Nat.Coprime (p ^ e) s := by
        rw [Nat.coprime_pow_left_iff (by omega)]
        exact (Nat.Prime.coprime_iff_not_dvd (primesP p hpP)).2 hps
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [hmeq] at hm1
        simp at hm1
      have hs1 : 1 ≤ s := by omega
      have hφs0 : φ s ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.totient_pos.2 hs1)
      have hpodd : ¬ 2 ∣ p := by
        intro h2p
        rcases (Nat.dvd_prime (primesP p hpP)).1 h2p with h1 | h2
        · omega
        · omega
      have hpe1 : 1 ≤ p ^ (e - 1) := Nat.one_le_pow _ _ (by omega)
      have hv2odd : padicValNat 2 (p ^ (e - 1)) = 0 := by
        rw [padicValNat.pow, v2_eq_zero_of_odd hpodd, mul_zero]
      have hpp0 : p ^ (e - 1) * (p - 1) ≠ 0 :=
        Nat.mul_ne_zero (by omega) (by omega)
      have hv2m : padicValNat 2 m.totient
          = padicValNat 2 (p - 1) + padicValNat 2 (φ s) := by
        have h1 : φ m = p ^ (e - 1) * (p - 1) * φ s := by
          rw [hmeq, Nat.totient_mul hpcop, Nat.totient_prime_pow (primesP p hpP) (by omega)]
        rw [h1, padicValNat.mul hpp0 hφs0, padicValNat.mul (by omega) (by omega),
          padicValNat.pow, v2_eq_zero_of_odd hpodd, mul_zero, zero_add]
      have hsub : Finset.filter (fun q => q ∣ m) P
          ⊆ insert p (Finset.filter (fun q => q ∣ s) P) := by
        intro q hq
        obtain ⟨hqP, hqdvd⟩ := Finset.mem_filter.1 hq
        rw [hmeq] at hqdvd
        simp only [Finset.mem_insert, Finset.mem_filter]
        by_cases hqp : q = p
        · left; exact hqp
        · refine Or.inr ⟨hqP, ?_⟩
          rcases (Nat.Prime.dvd_mul (primesP q hqP)).1 hqdvd with h1 | h2
          · exfalso
            have hqp2 : q ∣ p := Nat.Prime.dvd_of_dvd_pow (primesP q hqP) h1
            rcases (Nat.dvd_prime (primesP p hpP)).1 hqp2 with h3 | h4
            · have := threeP q hqP
              omega
            · exact hqp h4
          · exact h2
      have hs' : S m ≤ padicValNat 2 (p - 1) + S s := by
        have h1 : S m ≤ ∑ q ∈ insert p (Finset.filter (fun q => q ∣ s) P),
            padicValNat 2 (q - 1) :=
          Finset.sum_le_sum_of_subset hsub
        rw [Finset.sum_insert (show p ∉ Finset.filter (fun q => q ∣ s) P from
          fun hc => hps (Finset.mem_filter.1 hc).2)] at h1
        exact h1
      have hsodd : ¬ 2 ∣ s := by
        intro h2s
        apply hodd
        rw [hmeq, mul_comm]
        exact dvd_mul_of_dvd_left h2s (p ^ e)
      have hpe3 : 3 ≤ p ^ e :=
        calc 3 ≤ p := hp3
          _ = p ^ 1 := (Nat.pow_one p).symm
          _ ≤ p ^ e := Nat.pow_le_pow_right (show 0 < p by omega) (by omega : (1:Nat) ≤ e)
      have hsmlt : s < m := by
        have h1 : s + 1 ≤ p ^ e * s := by
          have h2 : s + 1 ≤ 2 * s := by omega
          have h3 : 2 * s ≤ p ^ e * s := Nat.mul_le_mul_right s (by omega)
          omega
        rw [hmeq]
        omega
      have hIH := ih s hsmlt hsodd
      omega
    · have hzero : ∀ q ∈ Finset.filter (fun q => q ∣ m) P, padicValNat 2 (q - 1) = 0 := by
        intro q hq
        exact absurd hq (fun hc => hS ⟨q, hc⟩)
      show (∑ p ∈ Finset.filter (fun q => q ∣ m) P, padicValNat 2 (p - 1))
        ≤ padicValNat 2 m.totient
      rw [Finset.sum_eq_zero hzero]
      omega

/-- Per-element bound: `v₂(φ m) + [2 ∣ m] ≥ v₂ m + S m`. -/
lemma per_k (m : ℕ) (hm : 1 ≤ m) :
    padicValNat 2 m + S m ≤ padicValNat 2 m.totient + (if 2 ∣ m then 1 else 0) := by
  by_cases h2 : 2 ∣ m
  · obtain ⟨e, s, he, hsodd, hmeq⟩ := exists_pow_mul m 2 (by omega) hm h2
    rw [hmeq]
    have hif : (if 2 ∣ 2 ^ e * s then 1 else 0) = 1 := if_pos (by rw [← hmeq]; exact h2)
    rw [hif]
    have hcop : Nat.Coprime (2 ^ e) s := by
      rw [Nat.coprime_pow_left_iff (by omega)]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hsodd
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [hmeq] at hm
      simp at hm
    have hs1 : 1 ≤ s := by omega
    have hφs0 : φ s ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.totient_pos.2 hs1)
    have hφ : φ (2 ^ e * s) = 2 ^ (e - 1) * φ s := by
      rw [Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two (by omega)]
      ring
    have h2e0 : 2 ^ e * s ≠ 0 := Nat.mul_ne_zero (by positivity) (by omega)
    have hv22 : padicValNat 2 2 = 1 := by norm_num
    have hv2m : padicValNat 2 (2 ^ e * s) = e := by
      rw [padicValNat.mul (by positivity) (by omega), padicValNat.pow, v2_eq_zero_of_odd hsodd,
        add_zero, hv22, Nat.mul_one]
    have h2pe1 : 1 ≤ 2 ^ (e - 1) := Nat.one_le_pow _ _ (by omega)
    have hv2φ : padicValNat 2 (φ (2 ^ e * s)) = (e - 1) + padicValNat 2 (φ s) := by
      rw [hφ, padicValNat.mul (by omega) hφs0, padicValNat.pow, hv22]
      ring
    have hSm : S (2 ^ e * s) ≤ S s := by
      refine Finset.sum_le_sum_of_subset ?_
      intro q hq
      obtain ⟨hqP, hqdvd⟩ := Finset.mem_filter.1 hq
      simp only [Finset.mem_filter]
      refine ⟨hqP, ?_⟩
      rcases (Nat.Prime.dvd_mul (primesP q hqP)).1 hqdvd with hq2 | hq2
      · exfalso
        have hq2d : q ∣ 2 := Nat.Prime.dvd_of_dvd_pow (primesP q hqP) hq2
        rcases (Nat.dvd_prime Nat.prime_two).1 hq2d with h1 | h2
        · have := threeP q hqP
          omega
        · have := threeP q hqP
          omega
      · exact hq2
    have hIH := S_le_v2_phi_odd s hsodd
    omega
  · have hv2m : padicValNat 2 m = 0 := v2_eq_zero_of_odd h2
    have hIH := S_le_v2_phi_odd m h2
    rw [if_neg h2]
    omega

/-- Count multiples: `#{k < n : q ∣ k+1} = n / q`. -/
lemma card_filter_dvd (q : ℕ) (_hq : 1 ≤ q) : ∀ n : ℕ,
    (Finset.filter (fun k => q ∣ k + 1) (Finset.range n)).card = n / q := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : q ∣ n + 1
    · have hmem : n ∉ Finset.filter (fun k => q ∣ k + 1) (Finset.range n) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [if_pos h, Finset.card_insert_of_notMem hmem, ih, Nat.succ_div]
      simp [h]
    · rw [if_neg h, ih, Nat.succ_div]
      simp [h]

lemma v2_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat 2 (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat 2 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValNat.mul
      (hf a (Finset.mem_insert_self a s))
      (Finset.prod_ne_zero_iff.2 (fun b hb => hf b (Finset.mem_insert_of_mem hb)))]
    rw [ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))]

/-- Main lower bound on `v₂` of the totient product. -/
lemma v2_B_bound (n : ℕ) :
    padicValNat 2 (n !) + ∑ p ∈ P, padicValNat 2 (p - 1) * (n / p)
      ≤ padicValNat 2 (∏ k ∈ Finset.range n, (k + 1).totient) + n / 2 := by
  have hφ0 : ∀ k ∈ Finset.range n, (k + 1).totient ≠ 0 := fun k _ =>
    Nat.pos_iff_ne_zero.mp (Nat.totient_pos.2 (Nat.succ_pos k))
  rw [v2_prod _ _ hφ0]
  have h1 : ∑ k ∈ Finset.range n, (padicValNat 2 (k + 1) + S (k + 1))
      ≤ ∑ k ∈ Finset.range n, (padicValNat 2 ((k+1).totient) + (if 2 ∣ k + 1 then 1 else 0)) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have hk1 : 1 ≤ k + 1 := Nat.succ_pos k
    have h := per_k (k + 1) hk1
    by_cases h2 : 2 ∣ k + 1
    · rw [if_pos h2] at h ⊢; omega
    · rw [if_neg h2] at h ⊢; omega
  have h2 : ∑ k ∈ Finset.range n, (if 2 ∣ k + 1 then 1 else 0) = n / 2 := by
    rw [← Finset.card_filter]
    rw [card_filter_dvd 2 (by omega) n]
  have h3 : ∑ k ∈ Finset.range n, padicValNat 2 (k + 1) = padicValNat 2 (n !) := by
    rw [← v2_prod _ _ (fun k _ => Nat.succ_ne_zero k), ← Finset.prod_range_add_one_eq_factorial]
  have h4 : ∑ k ∈ Finset.range n, S (k + 1)
      = ∑ p ∈ P, padicValNat 2 (p - 1) * (n / p) := by
    have hS : ∀ k, S (k + 1)
        = ∑ p ∈ P, (if p ∣ k + 1 then padicValNat 2 (p - 1) else 0) :=
      fun k => Finset.sum_filter (fun p => p ∣ k + 1) (fun p => padicValNat 2 (p - 1))
    rw [Finset.sum_congr rfl (fun k _ => hS k), Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_filter (fun k => p ∣ k + 1) (fun _ => padicValNat 2 (p - 1)),
      Finset.sum_const, card_filter_dvd p (by have := threeP p ‹p ∈ P›; omega),
      Nat.nsmul_eq_mul, mul_comm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h1
  omega

lemma hD1 : 3 * D ≤ 2 * num := by decide +kernel

lemma hD2 : 2 * bnd + 3 * D * 100 < 2 * num * 100 := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem bign (n : ℕ) (hn : 100 ≤ n) :
    ¬ ((∏ k ∈ Finset.range n, (k + 1).totient) ∣ ∏ k ∈ Finset.range n, (k + 1)^2) := by
  have hv2f : padicValNat 2 (n !) < n :=
    padicValNat_factorial_lt_of_ne_zero 2 (by omega : n ≠ 0)
  have hSbig : n + n / 2 ≤ ∑ p ∈ P, padicValNat 2 (p - 1) * (n / p) := by
    have hsum1 : ∀ p ∈ P,
        2 * (padicValNat 2 (p - 1) * (D / p)) * n
          ≤ 2 * D * (padicValNat 2 (p - 1) * (n / p))
            + 2 * (padicValNat 2 (p - 1) * (D / p) * (p - 1)) := by
      intro p hp
      have hp3 := threeP p hp
      have hpD : p ∣ D := Finset.dvd_prod_of_mem (fun q => q) hp
      have hDm : D / p * p = D := Nat.div_mul_cancel hpD
      have hkey : n ≤ p * (n / p) + (p - 1) := by
        have hdm : p * (n / p) + n % p = n := Nat.div_add_mod n p
        have hmod := Nat.mod_lt n (show 0 < p by omega)
        omega
      linear_combination 2 * (padicValNat 2 (p - 1) * (D / p)) * hkey
        + 2 * (padicValNat 2 (p - 1) * (n / p)) * hDm
    have hsummed : ∑ p ∈ P, 2 * (padicValNat 2 (p - 1) * (D / p)) * n
        ≤ ∑ p ∈ P, (2 * D * (padicValNat 2 (p - 1) * (n / p))
            + 2 * (padicValNat 2 (p - 1) * (D / p) * (p - 1))) :=
      Finset.sum_le_sum hsum1
    have hnumeq : ∑ p ∈ P, 2 * (padicValNat 2 (p - 1) * (D / p)) * n = 2 * num * n := by
      have hnum : num = ∑ p ∈ P, padicValNat 2 (p - 1) * (D / p) := rfl
      rw [hnum, Finset.mul_sum, Finset.sum_mul]
    have hbndeq : ∑ p ∈ P, (2 * D * (padicValNat 2 (p - 1) * (n / p))
          + 2 * (padicValNat 2 (p - 1) * (D / p) * (p - 1)))
        = 2 * D * (∑ p ∈ P, padicValNat 2 (p - 1) * (n / p)) + 2 * bnd := by
      have hbnd : bnd = ∑ p ∈ P, padicValNat 2 (p - 1) * (D / p) * (p - 1) := rfl
      rw [hbnd, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hnumeq, hbndeq] at hsummed
    have hlin : 3 * D * n + 1 + 2 * bnd ≤ 2 * num * n := by
      obtain ⟨s, hs⟩ : ∃ s, n = 100 + s := ⟨n - 100, by omega⟩
      have hA : 2 * bnd + 3 * D * 100 + 1 ≤ 2 * num * 100 := by
        have := hD2
        omega
      have hD : 3 * D * s ≤ 2 * num * s := Nat.mul_le_mul_right s hD1
      have hE : 3 * D * n = 3 * D * 100 + 3 * D * s := by rw [hs]; ring
      have hF : 2 * num * n = 2 * num * 100 + 2 * num * s := by rw [hs]; ring
      omega
    have hle : 2 * D * (n + n / 2) ≤ 3 * D * n := by
      have hstep : 2 * (n + n / 2) ≤ 3 * n := by omega
      calc 2 * D * (n + n / 2) = D * (2 * (n + n / 2)) := by ring
        _ ≤ D * (3 * n) := Nat.mul_le_mul_left D hstep
        _ = 3 * D * n := by ring
    have hfinal : 2 * D * (n + n / 2)
        ≤ 2 * D * (∑ p ∈ P, padicValNat 2 (p - 1) * (n / p)) := by omega
    exact Nat.le_of_mul_le_mul_left hfinal (show 0 < 2 * D by decide +kernel)
  have hB := v2_B_bound n
  have hv2B : 2 * padicValNat 2 (n !) + 1
      ≤ padicValNat 2 (∏ k ∈ Finset.range n, (k + 1).totient) := by omega
  have hv2A : padicValNat 2 (∏ k ∈ Finset.range n, (k + 1)^2)
      = 2 * padicValNat 2 (n !) := by
    rw [Finset.prod_pow, Finset.prod_range_add_one_eq_factorial, pow_two,
      padicValNat.mul (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero n)]
    omega
  intro hdvd
  have hA0 : ∏ k ∈ Finset.range n, (k + 1)^2 ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun k _ => pow_ne_zero _ (Nat.succ_ne_zero k))
  have h2dvdB : 2 ^ (2 * padicValNat 2 (n !) + 1) ∣ ∏ k ∈ Finset.range n, (k + 1).totient :=
    (Nat.pow_dvd_iff_le_padicValNat (by omega)
      (Finset.prod_ne_zero_iff.2 (fun k _ =>
        Nat.pos_iff_ne_zero.mp (Nat.totient_pos.2 (Nat.succ_pos k))))).mpr hv2B
  have h2A := h2dvdB.trans hdvd
  rw [Nat.pow_dvd_iff_le_padicValNat (by omega) hA0] at h2A
  rw [hv2A] at h2A
  omega

end BigN

/-- Membership characterization of `integerDetN`. -/
theorem mem_integerDetN_iff (n : ℕ) :
    n ∈ OeisA60841.integerDetN ↔ (n = 36 ∨ n = 38 ∨ (1 ≤ n ∧ n ≤ 34)) := by
  simp [OeisA60841.integerDetN]

/-- **Main theorem**: `1/det M` is an integer exactly for `n ∈ {1..34, 36, 38}`. -/
theorem swarm_proof : ∀ n : ℕ, 1 ≤ n →
    (((OeisA60841.lcmMatrix n).det)⁻¹.den = 1 ↔ n ∈ OeisA60841.integerDetN) := by
  intro n hn
  rw [den_bridge, mem_integerDetN_iff]
  by_cases h : n < 100
  · refine (classify n hn h).trans ?_
    constructor <;> rintro (h1 | h1 | h1) <;> omega
  · have h100 : 100 ≤ n := by omega
    constructor
    · intro hdvd
      exact (BigN.bign n h100 hdvd).elim
    · rintro (h36 | h38 | ⟨h1, h34⟩)
      · exact absurd h36 (by omega)
      · exact absurd h38 (by omega)
      · exact absurd h34 (by omega)
