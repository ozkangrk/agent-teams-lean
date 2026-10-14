
import FormalConjectures.OEIS.«46969»

open Finset

namespace Swarm46969

/-- If `x * d` is an integer then the denominator of `x` divides `d`. -/
lemma den_dvd {x : ℚ} {d : ℕ} (z : ℤ) (hz : x * (d : ℚ) = (z : ℚ)) : x.den ∣ d := by
  have h0 : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have h1 : (x.num : ℚ) * (d : ℚ) = (z : ℚ) * (x.den : ℚ) := by
    rw [← Rat.num_div_den x] at hz
    rw [← hz]
    field_simp
  have h2 : x.num * (d : ℤ) = z * (x.den : ℤ) := by exact_mod_cast h1
  have h3 : (x.den : ℤ) ∣ x.num * (d : ℤ) := ⟨z, by rw [h2, mul_comm]⟩
  have h4 : x.den ∣ (x.num * (d : ℤ)).natAbs := Int.ofNat_dvd_left.mp h3
  rw [Int.natAbs_mul] at h4
  simp only [Int.natAbs_natCast] at h4
  exact x.reduced.symm.dvd_of_dvd_mul_left h4



/-! ### `LD r x` : `x` lies in `r^2` times the localization away from `r` -/

/-- `LD r x` means `x = r * r * z / c` for integers `z` and `c` with `r ∤ c`. -/
def LD (r : ℕ) (x : ℚ) : Prop := ∃ z : ℤ, ∃ c : ℕ, c ≠ 0 ∧ ¬ r ∣ c ∧ x = (r * r * z : ℤ) / (c : ℚ)

lemma LD.add (hr : r.Prime) {x y : ℚ} (hx : LD r x) (hy : LD r y) : LD r (x + y) := by
  obtain ⟨z, c, hc0, hc, hx⟩ := hx
  obtain ⟨w, d, hd0, hd, hy⟩ := hy
  refine ⟨z * (d : ℤ) + w * (c : ℤ), c * d, mul_ne_zero hc0 hd0, ?_, ?_⟩
  · intro h
    obtain h' | h' := hr.dvd_mul.1 h
    exacts [hc h', hd h']
  · rw [hx, hy, div_add_div _ _ (by exact_mod_cast hc0) (by exact_mod_cast hd0), ← Nat.cast_mul]
    push_cast
    ring

lemma LD.neg {x : ℚ} (hx : LD r x) : LD r (-x) := by
  obtain ⟨z, c, hc0, hc, hx⟩ := hx
  exact ⟨-z, c, hc0, hc, by rw [hx, ← neg_div]; push_cast; ring⟩

lemma LD.mul_int {x : ℚ} (hx : LD r x) (y : ℤ) : LD r (x * y) := by
  obtain ⟨z, c, hc0, hc, hx⟩ := hx
  exact ⟨z * y, c, hc0, hc, by rw [hx]; push_cast; ring⟩

lemma LD.mul_nat {x : ℚ} (hx : LD r x) (y : ℕ) : LD r (x * y) := by
  exact_mod_cast hx.mul_int _

lemma LD.mul_r {x : ℚ} (hx : LD r x) : LD r (x * (r : ℚ)) := by
  obtain ⟨z, c, hc0, hc, hx⟩ := hx
  refine ⟨z * r, c, hc0, hc, ?_⟩
  rw [hx]; push_cast; ring

lemma LD.zero (hr : r.Prime) : LD r 0 := by
  refine ⟨0, 1, one_ne_zero, ?_, by norm_num⟩
  intro h
  have h2 := hr.one_lt
  have h3 : r ≤ 1 := Nat.le_of_dvd one_pos h
  omega

lemma LD.sum (hr : r.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, LD r (f i)) :
    LD r (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using LD.zero hr
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact LD.add hr (h a (Finset.mem_insert_self a s)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-! ### congruent sums -/

lemma sum_modEq {ι : Type*} (s : Finset ι) (f g : ι → ℤ) (n : ℤ)
    (h : ∀ i ∈ s, f i ≡ g i [ZMOD n]) : (∑ i ∈ s, f i) ≡ (∑ i ∈ s, g i) [ZMOD n] := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact Int.ModEq.add (h a (Finset.mem_insert_self a s)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-! ### Consequences of von Staudt–Clausen -/

/-- A prime dividing a product of primes divides (equals) one of them. -/
lemma prime_dvd_prod_mem (r : ℕ) (hr : r.Prime) (s : Finset ℕ) (h : r ∣ ∏ q ∈ s, q) :
    ∃ q ∈ s, r ∣ q := by
  classical
  induction s using Finset.induction with
  | empty => simp at h; exact absurd h hr.ne_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h
    obtain h1 | h2 := hr.dvd_mul.1 h
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨q, hqS, hq⟩ := ih h2
      exact ⟨q, Finset.mem_insert_of_mem hqS, hq⟩

/-- The set of primes `q` with `q - 1 ∣ i`. -/
def vsSet (i : ℕ) : Finset ℕ := (Finset.range (i + 2)).filter (fun q => q.Prime ∧ q - 1 ∣ i)

/-- The product of the primes `q` with `q - 1 ∣ i`. -/
def vsProd (i : ℕ) : ℕ := ∏ q ∈ vsSet i, q

lemma mem_vsSet {q i : ℕ} (h : q ∈ vsSet i) : q.Prime ∧ q - 1 ∣ i := Finset.mem_filter.1 h |>.2

lemma dvd_vsProd {q i : ℕ} (h : q ∈ vsSet i) : q ∣ vsProd i := by
  rw [vsProd]
  exact Finset.dvd_prod_of_mem (fun q => q) h

lemma vs_int {i : ℕ} (hi : Even i) : ∃ w : ℚ, w ∈ Set.range Int.cast ∧
    bernoulli i * ((vsProd i : ℕ) : ℚ) = w := by
  obtain ⟨k, hk0⟩ := hi
  have hk : i = 2 * k := by omega
  obtain ⟨w, hw⟩ := Bernoulli.vonStaudt_clausen k
  rw [← hk] at hw
  refine ⟨((w * (vsProd i : ℤ) - ∑ q ∈ vsSet i, ((vsProd i / q : ℕ) : ℤ) : ℤ) : ℚ), ⟨_, rfl⟩, ?_⟩
  have hw2 : bernoulli i + ∑ q ∈ vsSet i, (1 : ℚ) / q = ((w : ℤ) : ℚ) := hw.symm
  have hmul : (bernoulli i + ∑ q ∈ vsSet i, (1 : ℚ) / q) * ((vsProd i : ℕ) : ℚ)
      = ((w : ℤ) : ℚ) * ((vsProd i : ℕ) : ℚ) := by rw [hw2]
  rw [add_mul, Finset.sum_mul] at hmul
  have hsum : ∀ q ∈ vsSet i,
      ((1 : ℚ) / q) * ((vsProd i : ℕ) : ℚ) = ((vsProd i / q : ℕ) : ℚ) := by
    intro q hq
    have hqp : q.Prime := (mem_vsSet hq).1
    have hdvd : q ∣ vsProd i := dvd_vsProd hq
    rw [Nat.cast_div hdvd (by exact_mod_cast hqp.ne_zero), one_div_mul_eq_div]
  rw [Finset.sum_congr rfl (fun q hq => hsum q hq)] at hmul
  have hwit : (((w * (vsProd i : ℤ) - ∑ q ∈ vsSet i, ((vsProd i / q : ℕ) : ℤ) : ℤ) : ℤ) : ℚ)
      = ((w : ℤ) : ℚ) * ((vsProd i : ℕ) : ℚ) - ∑ q ∈ vsSet i, ((vsProd i / q : ℕ) : ℚ) := by
    rw [Int.cast_sub, Int.cast_mul, Int.cast_sum]
    push_cast only [Int.cast_natCast]
    try ring
  show bernoulli i * ((vsProd i : ℕ) : ℚ) = _
  rw [hwit]
  linarith [hmul]

lemma vs_den_dvd {i : ℕ} (hi : Even i) : (bernoulli i).den ∣ vsProd i := by
  obtain ⟨w, ⟨z, hz⟩, hw⟩ := vs_int hi
  exact den_dvd z (hz ▸ hw)

lemma vs_mem_of_dvd {i r : ℕ} (hr : r.Prime) (h : r ∣ vsProd i) : r ∈ vsSet i := by
  obtain ⟨q, hqS, hqr⟩ := prime_dvd_prod_mem r hr (vsSet i) h
  rcases (mem_vsSet hqS).1.eq_one_or_self_of_dvd r hqr with h1 | h1
  · exact absurd h1 hr.ne_one
  · rwa [← h1] at hqS

lemma vs_sqfree (i r : ℕ) (hr : r.Prime) : ¬ r * r ∣ vsProd i := by
  intro h
  have hmem : r ∈ vsSet i := vs_mem_of_dvd hr ((Nat.dvd_mul_right r r).trans h)
  have hE : r * ∏ q ∈ (vsSet i).erase r, q = vsProd i := by
    rw [vsProd, ← Finset.mul_prod_erase _ _ hmem]
  obtain ⟨k, hk⟩ := h
  rw [← hE, mul_assoc] at hk
  have h2 : r ∣ ∏ q ∈ (vsSet i).erase r, q := ⟨k, mul_left_cancel₀ hr.ne_zero hk⟩
  obtain ⟨q, hqS, hqr⟩ := prime_dvd_prod_mem r hr _ h2
  rcases (mem_vsSet (Finset.mem_of_mem_erase hqS)).1.eq_one_or_self_of_dvd r hqr with h1 | h1
  · exact absurd h1 hr.ne_one
  · exact absurd (h1 ▸ rfl) (Finset.mem_erase.1 hqS).1

lemma vs_dvd_den_iff {i r : ℕ} (hi : Even i) (hi2 : 0 < i) (hr : r.Prime) :
    r ∣ (bernoulli i).den ↔ r - 1 ∣ i := by
  constructor
  · intro h
    exact (mem_vsSet (vs_mem_of_dvd hr (h.trans (vs_den_dvd hi)))).2
  · intro hri
    by_contra hnd
    have hmem : r ∈ vsSet i := by
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hr, hri⟩
      have hr2 : 2 ≤ r := hr.one_lt
      have hle : r - 1 ≤ i := Nat.le_of_dvd hi2 hri
      omega
    have hE : r * ∏ q ∈ (vsSet i).erase r, q = vsProd i := by
      rw [vsProd, ← Finset.mul_prod_erase _ _ hmem]
    have hcop : (bernoulli i).den.Coprime r :=
      ((Nat.Prime.coprime_iff_not_dvd hr).2 hnd).symm
    have hdvdE : (bernoulli i).den ∣ ∏ q ∈ (vsSet i).erase r, q := by
      have h1 : (bernoulli i).den ∣ r * ∏ q ∈ (vsSet i).erase r, q := hE ▸ vs_den_dvd hi
      exact hcop.dvd_of_dvd_mul_right (by rwa [Nat.mul_comm])
    set E := ∏ q ∈ (vsSet i).erase r, q with hEdef
    set M := r * E with hMdef
    obtain ⟨w, hw⟩ := Bernoulli.vonStaudt_clausen (i / 2)
    have hii : 2 * (i / 2) = i := Nat.two_mul_div_two_of_even hi
    rw [hii] at hw
    have hw2 : bernoulli i + ∑ q ∈ vsSet i, (1 : ℚ) / q = ((w : ℤ) : ℚ) := hw.symm
    have hsplit : ∑ q ∈ vsSet i, (1 : ℚ) / q
        = (1 : ℚ) / r + ∑ q ∈ (vsSet i).erase r, (1 : ℚ) / q := by
      rw [← Finset.sum_erase_add _ _ hmem]; ring
    rw [hsplit] at hw2
    have hmul : (bernoulli i + ((1 : ℚ) / r + ∑ q ∈ (vsSet i).erase r, (1 : ℚ) / q)) * ((M : ℕ) : ℚ)
        = ((w : ℤ) : ℚ) * ((M : ℕ) : ℚ) := by rw [hw2]
    have h1q : ((1 : ℚ) / r) * ((M : ℕ) : ℚ) = ((E : ℕ) : ℚ) := by
      rw [hMdef, Nat.cast_mul, ← mul_assoc,
        div_mul_cancel₀ (1 : ℚ) (by exact_mod_cast hr.ne_zero), one_mul]
    have hEq : ∀ q ∈ (vsSet i).erase r,
        ((1 : ℚ) / q) * ((M : ℕ) : ℚ) = ((r : ℕ) : ℚ) * ((E / q : ℕ) : ℚ) := by
      intro q hq
      have hqE : q ∈ vsSet i := Finset.mem_of_mem_erase hq
      have hqp : q.Prime := (mem_vsSet hqE).1
      have hdvd : q ∣ E := Finset.dvd_prod_of_mem (fun q => q) hq
      rw [Nat.cast_div hdvd (by exact_mod_cast hqp.ne_zero), hMdef]
      field_simp
      push_cast
      ring
    rw [add_mul, add_mul, Finset.sum_mul, h1q,
      Finset.sum_congr rfl (fun q hq => hEq q hq), ← Finset.mul_sum] at hmul
    -- hmul : B * M + E + r * ∑ (E/q) = w * M
    obtain ⟨n, hn⟩ : ∃ n : ℕ, E = (bernoulli i).den * n := hdvdE
    have hBM : (bernoulli i) * ((M : ℕ) : ℚ) = (((bernoulli i).num * r * (n : ℕ) : ℤ) : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den (bernoulli i)]
      rw [hMdef, hn, Nat.cast_mul, Nat.cast_mul]
      have hd0 : ((bernoulli i).den : ℚ) ≠ 0 := by exact_mod_cast (bernoulli i).den_ne_zero
      rw [show (((r : ℚ)) * (((bernoulli i).den : ℚ) * ((n : ℚ))))
          = ((bernoulli i).den : ℚ) * (((r : ℚ)) * ((n : ℚ))) from by ring,
        ← mul_assoc, div_mul_cancel₀ _ hd0]
      push_cast
      ring
    rw [hBM] at hmul
    -- hmul : ↑(num*r*n) + ↑E + ↑r * Σ = ↑w * ↑(r*E), all in ℚ
    have hEint : ((E : ℕ) : ℤ) = (r : ℤ) * ((w : ℤ) * (E : ℤ)
        - ∑ q ∈ (vsSet i).erase r, ((E / q : ℕ) : ℤ)
        - ((bernoulli i).num * (n : ℕ) : ℤ)) := by
      apply Int.cast_injective (α := ℚ)
      have h2 := hmul
      rw [hMdef] at h2
      push_cast only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_sum,
        Int.cast_natCast, Nat.cast_mul] at h2 ⊢
      nlinarith [h2]
    have hrE : r ∣ E := Int.natCast_dvd_natCast.mp ⟨_, hEint⟩
    obtain ⟨q, hqS, hqr⟩ := prime_dvd_prod_mem r hr _ hrE
    rcases (mem_vsSet (Finset.mem_of_mem_erase hqS)).1.eq_one_or_self_of_dvd r hqr with h1 | h1
    · exact absurd h1 hr.ne_one
    · exact absurd (h1 ▸ rfl) (Finset.mem_erase.1 hqS).1

/-- If `r - 1 ∣ i` then the denominator of `Bᵢ` is `r * d` with `r ∣ d` false. -/
lemma vs_den_split {i r : ℕ} (hi : Even i) (hi2 : 0 < i) (hr : r.Prime) (h : r - 1 ∣ i) :
    ∃ d : ℕ, (bernoulli i).den = r * d ∧ ¬ r ∣ d := by
  have h1 : r ∣ (bernoulli i).den := (vs_dvd_den_iff hi hi2 hr).2 h
  refine ⟨(bernoulli i).den / r, (Nat.mul_div_cancel' h1).symm, ?_⟩
  intro hbad
  obtain ⟨k, hk⟩ := hbad
  have h2 : r * r ∣ (bernoulli i).den := by
    refine ⟨k, ?_⟩
    have hd : (bernoulli i).den = r * ((bernoulli i).den / r) := (Nat.mul_div_cancel' h1).symm
    rw [hd, hk, mul_assoc]
  exact vs_sqfree i r hr (h2.trans (vs_den_dvd hi))

/-! ### The specific primes `p` and `q = 2p - 1` -/

section Specific

variable {p : ℕ}

lemma divisors_of_two_mul_prime (hp : p.Prime) {d : ℕ} (hd : d ∣ 2 * p) :
    d = 1 ∨ d = 2 ∨ d = p ∨ d = 2 * p := by
  have hp1 : 2 ≤ p := hp.one_lt
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · exfalso
    rw [h0] at hd
    obtain ⟨k, hk⟩ := hd
    omega
  rcases Nat.even_or_odd d with hev | hev
  · obtain ⟨k, hk⟩ := hev
    have hkm : k ∣ p := by
      obtain ⟨m, hm⟩ := hd
      rw [hk] at hm
      have hm' : 2 * p = 2 * (k * m) := by rw [hm]; ring
      exact ⟨m, (Nat.mul_right_inj two_ne_zero).mp hm'⟩
    rcases hp.eq_one_or_self_of_dvd k hkm with h1 | h1
    · right; left; omega
    · right; right; right; omega
  · have hnd2 : ¬ 2 ∣ d := by
      intro hh
      have : d % 2 = 1 := Nat.odd_iff.mp hev
      omega
    have hcop : d.Coprime 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnd2).symm
    have hdp : d ∣ p := hcop.dvd_of_dvd_mul_left hd
    rcases hp.eq_one_or_self_of_dvd d hdp with h | h
    · left; omega
    · right; right; left; omega

lemma p_mod3 (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) : p % 3 = 1 := by
  have hne0 : p % 3 ≠ 0 := by
    intro h
    have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases hp.eq_one_or_self_of_dvd 3 this with h1 | h1
    · omega
    · omega
  have hne2 : p % 3 ≠ 2 := by
    intro h
    have h3dvd : 3 ∣ 2 * p - 1 := by omega
    rcases hp'.eq_one_or_self_of_dvd 3 h3dvd with h1 | h1
    · omega
    · omega
  omega

/-- von Staudt–Clausen at `2p`: `B_{2p} = N / 6` with `N` odd and `N ≡ 1 [MOD 3]`. -/
lemma B_2p_eq (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    ∃ N : ℤ, bernoulli (2 * p) = ((N : ℤ) : ℚ) / ((6 : ℕ) : ℚ) ∧ N % 2 = 1 ∧ N % 3 = 1 := by
  classical
  have hp1 : 2 ≤ p := hp.one_lt
  obtain ⟨w, hw⟩ := Bernoulli.vonStaudt_clausen p
  have hset : (Finset.range (2 * p + 2)).filter (fun q => q.Prime ∧ q - 1 ∣ 2 * p) = {2, 3} := by
    apply Finset.ext
    intro q
    constructor
    · intro hq
      obtain ⟨hmem, hqp, hdvd⟩ := Finset.mem_filter.1 hq
      have hlt : q < 2 * p + 2 := Finset.mem_range.1 hmem
      have hpod : p % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
      have hp5 : 5 ≤ p := by omega
      rcases divisors_of_two_mul_prime hp hdvd with h | h | h | h
      · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      · -- q - 1 = p, q = p + 1 even ≥ 6
        exfalso
        have hodd : p % 2 = 1 := hpod
        have h6 : 2 ∣ q := by omega
        rcases hqp.eq_one_or_self_of_dvd 2 h6 with h1 | h1
        · omega
        · omega
      · -- q - 1 = 2p, q = 2p+1 divisible by 3
        exfalso
        have hm3 := p_mod3 hp hp' h3
        have h3dvd : 3 ∣ q := by omega
        rcases hqp.eq_one_or_self_of_dvd 3 h3dvd with h1 | h1
        · omega
        · omega
    · intro hq
      rcases Finset.mem_insert.1 hq with h | h
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by
          rw [h]; exact Nat.prime_two, by rw [h]; simp⟩
      · rcases Finset.mem_singleton.1 h with h
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by
          rw [h]; exact Nat.prime_three, by rw [h]; simp⟩
  rw [hset] at hw
  have hsum : ∑ q ∈ ({2, 3} : Finset ℕ), (1 : ℚ) / q = (5 : ℚ) / ((6 : ℕ) : ℚ) := by
    simp [Finset.sum_insert]
    norm_num
  refine ⟨6 * w - 5, ?_, by omega, by omega⟩
  have hw2 : bernoulli (2 * p) + (5 : ℚ) / ((6 : ℕ) : ℚ) = ((w : ℤ) : ℚ) := by
    rw [hsum] at hw; exact hw.symm
  have h6 : ((6 : ℕ) : ℚ) ≠ 0 := by norm_num
  rw [eq_div_iff h6]
  have h7 : bernoulli (2 * p) * ((6 : ℕ) : ℚ) + (5 : ℚ) = ((w : ℤ) : ℚ) * ((6 : ℕ) : ℚ) := by
    have h8 : (bernoulli (2 * p) + (5 : ℚ) / ((6 : ℕ) : ℚ)) * ((6 : ℕ) : ℚ)
        = ((w : ℤ) : ℚ) * ((6 : ℕ) : ℚ) := by rw [hw2]
    rw [add_mul, div_mul_cancel₀ (5 : ℚ) h6] at h8
    exact h8
  push_cast at h7 ⊢
  linarith

end Specific

/-! ### binomial divisibility -/

lemma choose_three_eq (p : ℕ) (hp : p.Prime) (h3 : 3 < p) :
    (2 * p + 1).choose 3 * 3 = (2 * p + 1) * (p * (2 * p - 1)) := by
  have h1 := Nat.add_one_mul_choose_eq (2 * p - 1) 1
  rw [show 2 * p - 1 + 1 = 2 * p from by omega] at h1
  rw [Nat.choose_one_right] at h1
  norm_num at h1
  have h2 := Nat.add_one_mul_choose_eq (2 * p) 2
  norm_num at h2
  have h3' : (2 * p).choose 2 = p * (2 * p - 1) := by
    have hC : (2 * p).choose 2 * 2 = 2 * (p * (2 * p - 1)) := by
      rw [← h1, Nat.mul_assoc]
    exact (Nat.mul_right_inj two_ne_zero).mp
      (show 2 * ((2 * p).choose 2) = 2 * (p * (2 * p - 1)) from by
        rw [Nat.mul_comm]; exact hC)
  rw [h3'] at h2
  exact h2.symm

lemma dvd_choose_three_p (p : ℕ) (hp : p.Prime) (h3 : 3 < p) : p ∣ (2 * p + 1).choose 3 := by
  have h := choose_three_eq p hp h3
  have hp3 : p ≠ 3 := by omega
  have h1 : p ∣ (2 * p + 1) * (p * (2 * p - 1)) := by
    refine hp.dvd_mul.2 (Or.inr ?_)
    exact dvd_mul_right p (2 * p - 1)
  have h2 : p ∣ (2 * p + 1).choose 3 * 3 := by rw [h]; exact h1
  rcases hp.dvd_mul.1 h2 with h' | h'
  · exact h'
  · have hle : p ≤ 3 := Nat.le_of_dvd three_pos h'
    omega

lemma dvd_choose_three_q (p : ℕ) (hp : p.Prime) (h3 : 3 < p) (hp' : (2 * p - 1).Prime) :
    (2 * p - 1) ∣ (2 * p + 1).choose 3 := by
  have hq3 : (2 * p - 1) ≠ 3 := by omega
  have h1 : (2 * p - 1) ∣ (2 * p + 1) * (p * (2 * p - 1)) :=
    dvd_mul_of_dvd_right (dvd_mul_left (2 * p - 1) p) (2 * p + 1)
  have h := choose_three_eq p hp h3
  have h2 : (2 * p - 1) ∣ (2 * p + 1).choose 3 * 3 := by rw [h]; exact h1
  rcases hp'.dvd_mul.1 h2 with h' | h'
  · exact h'
  · have hle : (2 * p - 1) ≤ 3 := Nat.le_of_dvd three_pos h'
    omega

lemma dvd_choose_p_sub_one (p : ℕ) (hp : p.Prime) (h3 : 3 < p) :
    p ∣ (2 * p + 1).choose (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
    omega
  have hm1 : (2 * p + 1) % p = 1 := by
    rw [show 2 * p + 1 = 1 + p * 2 from by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  have hm2 : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
  have hd1 : (2 * p + 1) / p = 2 := by
    rw [show 2 * p + 1 = 1 + p * 2 from by omega, Nat.add_mul_div_left 1 2 (by omega),
      Nat.div_eq_of_lt (by omega)]
  have hd2 : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := 2 * p + 1) (k := p - 1) (p := p)
  rw [hm1, hm2, hd1, hd2] at h
  rw [show (1 : ℕ).choose (p - 1) = 0 from Nat.choose_eq_zero_of_lt (by omega),
    show (2 : ℕ).choose 0 = 1 from Nat.choose_zero_right 2] at h
  norm_num at h
  have h2 : ((2 * p + 1).choose (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ)] := h
  rw [Int.modEq_zero_iff_dvd] at h2
  exact_mod_cast h2

/-- Constructor for `LD`. -/
lemma LD.of_frac (r : ℕ) (hr : r.Prime) (A : ℤ) (B : ℕ) (hB0 : 0 < B) (hB : ¬ r ∣ B) (k : ℕ)
    (hk : 2 ≤ k) :
    LD r (((A : ℤ) : ℚ) * ((r : ℕ) : ℚ) ^ k / ((B : ℕ) : ℚ)) := by
  have hk' : 2 + (k - 2) = k := by omega
  have hkey : ((r : ℕ) : ℚ) ^ k = ((r : ℕ) : ℚ) ^ 2 * ((r : ℕ) : ℚ) ^ (k - 2) := by
    rw [← pow_add, hk']
  refine ⟨A * (r : ℤ) ^ (k - 2), B, hB0.ne', hB, ?_⟩
  rw [hkey]
  push_cast
  ring

/-- Junk term when `r` does not divide the denominator of `Bᵢ`. -/
lemma LD_junk_generic {p r : ℕ} (hr : r.Prime) (hrN : ¬ r ∣ 2 * p + 1) {i : ℕ}
    (hnd : ¬ r ∣ (bernoulli i).den) (he : 3 ≤ 2 * p + 1 - i) :
    LD r (bernoulli i * ((2 * p + 1).choose i) * ((r : ℕ) : ℚ) ^ (2 * p + 1 - i)
      / ((2 * p + 1 : ℕ) : ℚ)) := by
  have hdpos := (bernoulli i).den_pos
  have hdq : (((bernoulli i).den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (bernoulli i).den_ne_zero
  have h2p1 : ((2 * p + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 2 * p + 1 ≠ 0)
  have key : (bernoulli i * ((2 * p + 1).choose i) * ((r : ℕ) : ℚ) ^ (2 * p + 1 - i)
      / ((2 * p + 1 : ℕ) : ℚ))
      = ((((bernoulli i).num * ((2 * p + 1).choose i : ℤ) : ℤ)) : ℚ)
          * ((r : ℕ) : ℚ) ^ (2 * p + 1 - i)
        / (((bernoulli i).den * (2 * p + 1) : ℕ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den (bernoulli i)]
    rw [Nat.cast_mul]
    field_simp
    push_cast
    ring
  rw [key]
  have hdpos := (bernoulli i).den_pos
  refine LD.of_frac r hr _ ((bernoulli i).den * (2 * p + 1)) (Nat.mul_pos hdpos (by omega)) ?_
    (2 * p + 1 - i) (by omega)
  intro hdvd
  rcases hr.dvd_mul.1 hdvd with h' | h'
  · exact hnd h'
  · exact hrN h'

/-- Junk term when the denominator of `Bᵢ` is `r * d` with `r ∤ d`, and `r ∣ choose`. -/
lemma LD_junk_special {p r : ℕ} (hr : r.Prime) (hrN : ¬ r ∣ 2 * p + 1) {i d : ℕ}
    (hden : (bernoulli i).den = r * d) (hnd : ¬ r ∣ d) (hC : r ∣ (2 * p + 1).choose i)
    (he : 3 ≤ 2 * p + 1 - i) :
    LD r (bernoulli i * ((2 * p + 1).choose i) * ((r : ℕ) : ℚ) ^ (2 * p + 1 - i)
      / ((2 * p + 1 : ℕ) : ℚ)) := by
  obtain ⟨C', hC'⟩ := hC
  have hdpos := (bernoulli i).den_pos
  have hdne : d ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hden
    omega
  have hrq : ((r : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hdq : ((d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hdne
  have h2p1 : ((2 * p + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 2 * p + 1 ≠ 0)
  have key : (bernoulli i * ((2 * p + 1).choose i) * ((r : ℕ) : ℚ) ^ (2 * p + 1 - i)
      / ((2 * p + 1 : ℕ) : ℚ))
      = ((((bernoulli i).num * (C' : ℕ) : ℤ)) : ℚ) * ((r : ℕ) : ℚ) ^ (2 * p + 1 - i)
        / (((d * (2 * p + 1) : ℕ) : ℚ)) := by
    conv_lhs => rw [← Rat.num_div_den (bernoulli i)]
    rw [hden, hC', Nat.cast_mul, Nat.cast_mul]
    field_simp
    push_cast
    ring
  rw [key]
  refine LD.of_frac r hr _ (d * (2 * p + 1)) (Nat.mul_pos (Nat.pos_of_ne_zero hdne) (by omega)) ?_ (2 * p + 1 - i)
    (by omega)
  intro hdvd
  rcases hr.dvd_mul.1 hdvd with h' | h'
  · exact hnd h'
  · exact hrN h'

/-- Every Faulhaber term except `i = 2p` is `r^2`-divisible away from `r`. -/
lemma junk_term {p r : ℕ} (hp : p.Prime) (h3 : 3 < p) (hp' : (2 * p - 1).Prime) (hr : r.Prime)
    (hrp : r = p ∨ r = 2 * p - 1) (i : ℕ) (hi : i ≤ 2 * p) (hine : i ≠ 2 * p) :
    LD r (bernoulli i * ((2 * p + 1).choose i) * ((r : ℕ) : ℚ) ^ (2 * p + 1 - i)
      / ((2 * p + 1 : ℕ) : ℚ)) := by
  classical
  have hp5 : 5 ≤ p := by
    have := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
    omega
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
  have hrN : ¬ r ∣ 2 * p + 1 := by
    intro hdvd
    rcases hrp with h | h
    · rw [h] at hdvd
      have h1 : p ∣ (2 * p + 1) - 2 * p := Nat.dvd_sub hdvd ⟨2, Nat.mul_comm 2 p⟩
      rw [show (2 * p + 1) - 2 * p = 1 from by omega] at h1
      have h2 : p = 1 := Nat.dvd_one.mp h1
      have := hp.one_lt
      omega
    · rw [h] at hdvd
      have h1 : (2 * p - 1) ∣ 2 := by
        have hh : (2 * p - 1) ∣ (2 * p + 1) - (2 * p - 1) :=
          Nat.dvd_sub hdvd (dvd_refl _)
        rw [show (2 * p + 1) - (2 * p - 1) = 2 from by omega] at hh
        exact hh
      have h2 : 2 * p - 1 ≤ 2 := Nat.le_of_dvd two_pos h1
      omega
  have hr1dvd : r - 1 ∣ 2 * p - 2 := by
    rcases hrp with h | h
    · rw [h]; exact ⟨2, by omega⟩
    · rw [h]; exact dvd_refl _
  have hrC3 : r ∣ (2 * p + 1).choose 3 := by
    rcases hrp with h | h
    · rw [h]; exact dvd_choose_three_p p hp h3
    · rw [h]; exact dvd_choose_three_q p hp h3 hp'
  have hgen : 2 ≤ i → i ≤ 2 * p - 4 → i ≠ p - 1 ∨ r ≠ p → ¬ (r - 1 ∣ i) := by
    intro hi2 hilt hpm hdvd
    rcases hrp with h | h
    · rw [h] at hdvd
      have hne : i ≠ p - 1 := by
        rcases hpm with h1 | h1
        · exact h1
        · omega
      obtain ⟨t, ht⟩ := hdvd
      rcases t with _ | _ | t
      · norm_num at ht
        omega
      · norm_num at ht
        exact hne ht
      · have ht' : i = (p - 1) * (t + 2) := ht
        have hle : 2 * (p - 1) ≤ (p - 1) * (t + 2) := by
          rw [Nat.mul_comm]
          exact Nat.mul_le_mul_left (p - 1) (show 2 ≤ t + 2 by omega)
        omega
    · rw [h] at hdvd
      have h1 : 2 * p - 2 ≤ i := by
        have hh := Nat.le_of_dvd (show 0 < i by omega) hdvd
        have hhh : 2 * p - 1 - 1 = 2 * p - 2 := by omega
        rw [hhh] at hh
        exact hh
      omega
  rcases Nat.even_or_odd i with hei | hei
  · rcases Nat.eq_zero_or_pos i with rfl | hipos
    · have hkey : (bernoulli 0 * ((2 * p + 1).choose 0) * ((r : ℕ) : ℚ) ^ (2 * p + 1 - 0)
          / ((2 * p + 1 : ℕ) : ℚ))
          = (((1 : ℤ) : ℚ) * ((r : ℕ) : ℚ) ^ (2 * p + 1) / ((2 * p + 1 : ℕ) : ℚ)) := by
        simp [bernoulli_zero]
      rw [hkey]
      exact LD.of_frac r hr 1 (2 * p + 1) (by omega) hrN (2 * p + 1) (by omega)
    -- even, positive
    have hmod : i % 2 = 0 := Nat.even_iff.mp hei
    have hne2m1 : i ≠ 2 * p - 1 := by omega
    have hile : i ≤ 2 * p - 2 := by omega
    have he3 : 3 ≤ 2 * p + 1 - i := by omega
    by_cases hi2m2 : i = 2 * p - 2
    · have hcs : (2 * p + 1).choose i = (2 * p + 1).choose 3 := by
        rw [hi2m2]
        have h4 : 3 ≤ 2 * p + 1 := by omega
        have h5 := Nat.choose_symm h4
        rw [show 2 * p + 1 - 3 = 2 * p - 2 from by omega] at h5
        exact h5
      have hr1 : r - 1 ∣ i := by rw [hi2m2]; exact hr1dvd
      obtain ⟨d, hd, hnd⟩ := vs_den_split hei hipos hr hr1
      exact LD_junk_special hr hrN hd hnd (by rw [hcs]; exact hrC3) he3
    · have hilt : i ≤ 2 * p - 4 := by omega
      by_cases hipm1 : i = p - 1
      · rcases hrp with h | h
        · have hr1 : r - 1 ∣ i := by
            rw [h, hipm1]
          obtain ⟨d, hd, hnd⟩ := vs_den_split hei hipos hr hr1
          have hcp : r ∣ (2 * p + 1).choose i := by
            rw [h, hipm1]
            exact dvd_choose_p_sub_one p hp h3
          exact LD_junk_special hr hrN hd hnd hcp he3
        · have hnr1 : ¬ (r - 1 ∣ i) := by
            intro hdvd
            exact hgen (by omega) hilt (Or.inr (by rw [h]; omega)) hdvd
          have hnd : ¬ r ∣ (bernoulli i).den := fun hh => hnr1 ((vs_dvd_den_iff hei hipos hr).1 hh)
          exact LD_junk_generic hr hrN hnd he3
      · have hnr1 : ¬ (r - 1 ∣ i) := by
          intro hdvd
          exact hgen (by omega) hilt (Or.inl hipm1) hdvd
        have hnd : ¬ r ∣ (bernoulli i).den := fun hh => hnr1 ((vs_dvd_den_iff hei hipos hr).1 hh)
        exact LD_junk_generic hr hrN hnd he3
  · by_cases hi1 : i = 1
    · rw [hi1]
      have hkey : (bernoulli 1 * ((2 * p + 1).choose 1) * ((r : ℕ) : ℚ) ^ (2 * p + 1 - 1)
          / ((2 * p + 1 : ℕ) : ℚ))
          = (((-1 : ℤ) : ℚ) * ((r : ℕ) : ℚ) ^ (2 * p)
            / ((2 : ℕ) : ℚ)) := by
        rw [bernoulli_one, Nat.choose_one_right, show 2 * p + 1 - 1 = 2 * p from by omega]
        have hrq : ((r : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
        have h2p1 : ((2 * p + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 2 * p + 1 ≠ 0)
        have h2 : ((2 : ℕ) : ℚ) ≠ 0 := by norm_num
        field_simp
        push_cast
        ring
      rw [hkey]
      refine LD.of_frac r hr (-1 : ℤ) 2 (by omega) ?_ (2 * p) (by omega)
      intro hdvd
      have hle : r ≤ 2 := Nat.le_of_dvd two_pos hdvd
      omega
    · have hmod : i % 2 = 1 := Nat.odd_iff.mp hei
      have hz : bernoulli i = 0 := bernoulli_eq_zero_of_odd hei (by omega)
      simp only [hz, zero_mul, zero_div]
      exact LD.zero hr

/-! ### Faulhaber extraction -/

/-- Faulhaber's formula at `r`, exponent `2p`: the power sum is `r * B_{2p}` plus junk. -/
lemma faulhaber_key {p r : ℕ} (hp : p.Prime) (h3 : 3 < p) (hp' : (2 * p - 1).Prime) (hr : r.Prime)
    (hrp : r = p ∨ r = 2 * p - 1) :
    (∑ k ∈ Finset.range r, ((k : ℕ) : ℚ) ^ (2 * p))
      = ((r : ℕ) : ℚ) * bernoulli (2 * p)
        + ∑ i ∈ (Finset.range (2 * p + 1)).erase (2 * p),
            (bernoulli i * ((2 * p + 1).choose i) * ((r : ℕ) : ℚ) ^ (2 * p + 1 - i)
              / ((2 * p + 1 : ℕ) : ℚ)) := by
  classical
  have h1 := sum_range_pow r (2 * p)
  have h2 := Finset.sum_erase_add (Finset.range (2 * p + 1))
    (fun i => bernoulli i * ((2 * p + 1).choose i) * ((r : ℕ) : ℚ) ^ (2 * p + 1 - i)
      / ((2 * p + 1 : ℕ) : ℚ))
    (Finset.mem_range.2 (show 2 * p < 2 * p + 1 by omega))
  have h3' : (bernoulli (2 * p) * ((2 * p + 1).choose (2 * p)) * ((r : ℕ) : ℚ)
        ^ (2 * p + 1 - 2 * p) / ((2 * p + 1 : ℕ) : ℚ))
      = ((r : ℕ) : ℚ) * bernoulli (2 * p) := by
    have hc : (2 * p + 1).choose (2 * p) = 2 * p + 1 := Nat.choose_succ_self_right (2 * p)
    have hpw : 2 * p + 1 - 2 * p = 1 := by omega
    rw [hc, hpw, pow_one]
    have hrq : ((r : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
    have h2p1 : ((2 * p + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 2 * p + 1 ≠ 0)
    field_simp
  rw [h1]
  simp only [← Nat.cast_succ]
  rw [← h2, h3']
  ring

/-- The whole power sum minus `r * B_{2p}` is junk. -/
lemma faulhaber_LD {p r : ℕ} (hp : p.Prime) (h3 : 3 < p) (hp' : (2 * p - 1).Prime) (hr : r.Prime)
    (hrp : r = p ∨ r = 2 * p - 1) :
    LD r ((∑ k ∈ Finset.range r, ((k : ℕ) : ℚ) ^ (2 * p)) - ((r : ℕ) : ℚ) * bernoulli (2 * p)) := by
  rw [faulhaber_key hp h3 hp' hr hrp, add_sub_cancel_left]
  refine LD.sum hr _ _ (fun i hi => junk_term hp h3 hp' hr hrp i ?_ (Finset.mem_erase.1 hi).1)
  have hmem : i < 2 * p + 1 := Finset.mem_range.1 (Finset.mem_of_mem_erase hi)
  exact by omega

/-! ### the doubling congruence -/

lemma sub_mul_pow_modEq (r x t : ℤ) (n : ℕ) :
    (x - r * t) ^ n ≡ x ^ n - (n : ℤ) * x ^ (n - 1) * (r * t) [ZMOD r * r] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      show (x - r * t) ^ 1 ≡ x ^ 1 - (1 : ℤ) * x ^ (1 - 1) * (r * t) [ZMOD r * r]
      simp only [pow_one, Nat.sub_self, pow_zero, Nat.cast_one, one_mul]
      exact Int.ModEq.refl _
    · rw [show n + 1 - 1 = n from by omega]
      have hnorm : x ^ n = x ^ (n - 1) * x := by
        rw [← pow_succ x (n - 1)]
        congr 1
        omega
      have key1 : (x ^ n - (n : ℤ) * x ^ (n - 1) * (r * t)) * x
          = x ^ (n + 1) - (n : ℤ) * x ^ n * (r * t) := by
        rw [pow_succ, hnorm]
        ring
      have key2 : (x ^ n - (n : ℤ) * x ^ (n - 1) * (r * t)) * (r * t) ≡ x ^ n * (r * t)
          [ZMOD r * r] := by
        rw [Int.modEq_iff_dvd]
        have he : x ^ n * (r * t) - (x ^ n - (n : ℤ) * x ^ (n - 1) * (r * t)) * (r * t)
            = r * r * ((n : ℤ) * x ^ (n - 1) * t * t) := by
          rw [hnorm]
          ring
        rw [he]
        exact dvd_mul_right _ _
      have hc := ih.mul (Int.ModEq.refl (x - r * t))
      rw [pow_succ]
      refine hc.trans ?_
      have hA : (x ^ n - (n : ℤ) * x ^ (n - 1) * (r * t)) * (x - r * t)
          = (x ^ n - (n : ℤ) * x ^ (n - 1) * (r * t)) * x
            - (x ^ n - (n : ℤ) * x ^ (n - 1) * (r * t)) * (r * t) := by ring
      rw [hA, key1]
      have hbb := (Int.ModEq.refl
        (x ^ (n + 1) - (n : ℤ) * x ^ n * (r * t))).sub key2
      refine hbb.trans ?_
      rw [Int.modEq_iff_dvd]
      have hz : (x ^ (n + 1) - ((n + 1 : ℤ)) * x ^ n * (r * t))
          - ((x ^ (n + 1) - (n : ℤ) * x ^ n * (r * t)) - x ^ n * (r * t)) = 0 := by
        push_cast
        ring
      norm_num at hz ⊢
      rw [hz]
      exact dvd_zero _

/-! ### Fermat little theorem -/

lemma fermat_zmod (q : ℕ) (hq : q.Prime) (a : ℤ) (ha : ¬ ((q : ℤ)) ∣ a) :
    a ^ (q - 1) ≡ 1 [ZMOD (q : ℤ)] := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h0 : (a : ZMod q) ≠ 0 := by
    intro hh
    exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a q).1 hh)
  have h1 : ((a : ZMod q)) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h0
  have h2 : (((a ^ (q - 1) : ℤ)) : ZMod q) = ((1 : ℤ) : ZMod q) := by
    rw [Int.cast_pow, h1, Int.cast_one]
  exact ZMod.intCast_eq_intCast_iff (a ^ (q - 1)) 1 q |>.1 h2

lemma modEq_of_mod (n a b : ℤ) (h : a % n = b % n) : a ≡ b [ZMOD n] := by
  rw [Int.modEq_iff_dvd]
  refine (Int.dvd_iff_emod_eq_zero).2 ?_
  rw [Int.sub_emod, ← h, sub_self, Int.zero_emod]

/-! ### permutation by doubling -/

lemma perm_two_mod (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) (f : ℕ → ℤ) :
    ∑ k ∈ Finset.range r, f ((2 * k) % r) = ∑ k ∈ Finset.range r, f k := by
  classical
  have hrodd : r % 2 = 1 := by
    have := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hr hr2)
    omega
  have hinj : ∀ k ∈ Finset.range r, ∀ k' ∈ Finset.range r, (2 * k) % r = (2 * k') % r → k = k' := by
    intro k hk k' hk' h
    have hm : (((2 * k : ℕ) : ℤ)) % ((r : ℤ)) = (((2 * k' : ℕ) : ℤ)) % ((r : ℤ)) := by
      push_cast
      exact_mod_cast h
    have hd := modEq_of_mod ((r : ℤ)) _ _ hm
    rw [Int.modEq_iff_dvd] at hd
    have hc : ((2 : ℤ)) * (((k' : ℤ)) - ((k : ℤ))) = (((2 * k' : ℕ) : ℤ)) - (((2 * k : ℕ) : ℤ)) := by
      push_cast
      ring
    rw [← hc] at hd
    have hcop : IsCoprime ((2 : ℤ)) ((r : ℤ)) := by
      refine Nat.isCoprime_iff_coprime.2 ?_
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_
      intro hdvd
      omega
    have hd2 : ((r : ℤ)) ∣ (((k : ℤ)) - ((k' : ℤ))) := by
      have hz := hcop.symm.dvd_of_dvd_mul_left hd
      obtain ⟨j, hj⟩ := hz
      exact ⟨-j, by linarith [hj]⟩
    have hk1 := Finset.mem_range.1 hk
    have hk2 := Finset.mem_range.1 hk'
    have habs : r ∣ ((k : ℤ) - ((k' : ℤ))).natAbs := Int.ofNat_dvd_left.mp hd2
    have hlt : ((k : ℤ) - ((k' : ℤ))).natAbs < r := by
      rcases le_or_gt ((k : ℤ)) ((k' : ℤ)) with hh | hh
      · rcases Int.natAbs_eq (((k : ℤ)) - ((k' : ℤ))) with h1 | h1
        · omega
        · have : ((k : ℕ) - (k' : ℕ)) < r := by omega
          push_cast
          omega
      · rcases Int.natAbs_eq (((k : ℤ)) - ((k' : ℤ))) with h1 | h1
        · push_cast at h1
          omega
        · omega
    have h0 : ((k : ℤ) - ((k' : ℤ))).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt habs hlt
    have : ((k : ℤ)) - ((k' : ℤ)) = 0 := Int.natAbs_eq_zero.mp h0
    omega
  have hinjOn : Set.InjOn (fun k => (2 * k) % r) ↑(Finset.range r) := by
    intro x hx y hy hxy
    have hx' : x ∈ Finset.range r := by simpa using hx
    have hy' : y ∈ Finset.range r := by simpa using hy
    exact (hinj y hy' x hx' hxy.symm).symm
  have hsub : (Finset.range r).image (fun k => (2 * k) % r) ⊆ Finset.range r := by
    intro q hq
    simp only [Finset.mem_image] at hq
    obtain ⟨k, _, hkq⟩ := hq
    refine Finset.mem_range.2 ?_
    rw [← hkq]
    exact Nat.mod_lt _ hr.pos
  have himg : (Finset.range r).image (fun k => (2 * k) % r) = Finset.range r :=
    Finset.eq_of_subset_of_card_le hsub
      (le_of_eq (Finset.card_image_of_injOn hinjOn).symm)
  rw [← Finset.sum_image (f := f) (g := fun k => (2 * k) % r) (s := Finset.range r) hinjOn, himg]

/-! ### Fermat at our primes -/

lemma two_pow_mod (p : ℕ) (hp : p.Prime) (h3 : 3 < p) (r : ℕ) (hr : r.Prime)
    (hrp : r = p ∨ r = 2 * p - 1) : ((2 : ℤ)) ^ (2 * p) ≡ 4 [ZMOD ((r : ℤ))] := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
  have hf : ((2 : ℤ)) ^ (r - 1) ≡ 1 [ZMOD ((r : ℤ))] := by
    refine fermat_zmod r hr _ ?_
    intro hdvd
    have hle : ((r : ℤ)) ∣ ((2 : ℤ)) := hdvd
    have hr2 : r ≤ 2 := Nat.le_of_dvd two_pos (by exact_mod_cast hle)
    rcases hrp with h1 | h1 <;> omega
  have hrp2 : r = p ∨ r = 2 * p - 1 := hrp
  rcases hrp with h | h
  · have h2 : 2 * p = 2 * (r - 1) + 2 := by
      rcases hrp2 with h1 | h1 <;> omega
    have hconv : ((2 : ℤ)) ^ (2 * (r - 1)) = ((2 : ℤ)) ^ ((r - 1) * 2) := by
      congr 1
      omega
    rw [h2, pow_add, hconv, pow_mul]
    calc (((2 : ℤ)) ^ (r - 1)) ^ 2 * 2 ^ 2
        ≡ ((1 : ℤ)) ^ 2 * 4 [ZMOD ((r : ℤ))] := by
          exact Int.ModEq.mul (hf.pow 2) (Int.ModEq.refl _)
      _ = 4 := by norm_num
  · have h2 : 2 * p = (r - 1) + 2 := by
      rcases hrp2 with h1 | h1 <;> omega
    rw [h2, pow_add]
    calc ((2 : ℤ)) ^ (r - 1) * 2 ^ 2
        ≡ ((1 : ℤ)) * 4 [ZMOD ((r : ℤ))] := by
          exact Int.ModEq.mul hf (Int.ModEq.refl _)
      _ = 4 := by norm_num

/-! ### coprimality helper -/

lemma coprime_12q (x : ℕ) (h2 : ¬ 2 ∣ x) (h3 : ¬ 3 ∣ x) {q : ℕ} (hq : Nat.Prime q) (hqd : ¬ q ∣ x) :
    Nat.Coprime x (12 * q) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h
  obtain ⟨r, hr1, hr2⟩ := Nat.exists_prime_and_dvd h
  have hxr : r ∣ x := hr2.trans (Nat.gcd_dvd_left x (12 * q))
  have h12 : r ∣ 12 * q := hr2.trans (Nat.gcd_dvd_right x (12 * q))
  rcases (Nat.Prime.dvd_mul hr1).1 h12 with h' | h'
  · have h'2 : r ∣ 4 * 3 := by rwa [show (12 : ℕ) = 4 * 3 from rfl] at h'
    rcases (Nat.Prime.dvd_mul hr1).1 h'2 with h'' | h''
    · have h4 : r ∣ 2 * 2 := by rwa [show (4 : ℕ) = 2 * 2 from rfl] at h''
      rcases (Nat.Prime.dvd_mul hr1).1 h4 with h3' | h3'
      · rcases Nat.prime_two.eq_one_or_self_of_dvd r h3' with h1 | h1
        · exact absurd h1 hr1.ne_one
        · exact h2 (h1 ▸ hxr)
      · rcases Nat.prime_two.eq_one_or_self_of_dvd r h3' with h1 | h1
        · exact absurd h1 hr1.ne_one
        · exact h2 (h1 ▸ hxr)
    · rcases Nat.prime_three.eq_one_or_self_of_dvd r h'' with h1 | h1
      · exact absurd h1 hr1.ne_one
      · exact h3 (h1 ▸ hxr)
  · rcases hq.eq_one_or_self_of_dvd r h' with h1 | h1
    · exact absurd h1 hr1.ne_one
    · exact hqd (h1 ▸ hxr)

/-! ### the doubling congruence -/

lemma doubling (p r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) :
    (∑ k ∈ Finset.range r, ((k : ℕ) : ℤ) ^ (2 * p)) ≡
      ((2 : ℤ)) ^ (2 * p) * (∑ k ∈ Finset.range r, ((k : ℕ) : ℤ) ^ (2 * p))
        - ((2 * p : ℤ)) * ((r : ℤ)) *
          (∑ k ∈ Finset.range r, ((2 * k : ℕ) : ℤ) ^ (2 * p - 1)
            * (((2 * k : ℕ) : ℤ) / ((r : ℤ))))
      [ZMOD ((r : ℤ)) * ((r : ℤ))] := by
  classical
  set T' := ∑ k ∈ Finset.range r, ((2 * k : ℕ) : ℤ) ^ (2 * p - 1)
    * (((2 * k : ℕ) : ℤ) / ((r : ℤ))) with hT'
  have hper : ∀ k ∈ Finset.range r,
      (((2 * k) % r : ℕ) : ℤ) ^ (2 * p) ≡ ((2 * k : ℕ) : ℤ) ^ (2 * p)
        - ((2 * p : ℤ)) * ((2 * k : ℕ) : ℤ) ^ (2 * p - 1)
          * (((r : ℤ)) * (((2 * k : ℕ) : ℤ) / ((r : ℤ))))
        [ZMOD ((r : ℤ)) * ((r : ℤ))] := by
    intro k _
    have hmod : (((2 * k) % r : ℕ) : ℤ)
        = ((2 * k : ℕ) : ℤ) - ((r : ℤ)) * (((2 * k : ℕ) : ℤ) / ((r : ℤ))) := by
      rw [Int.natCast_mod, EuclideanDomain.mod_eq_sub_mul_div]
    rw [hmod]
    exact sub_mul_pow_modEq ((r : ℤ)) _ _ _
  have hsum := sum_modEq (Finset.range r)
    (fun k => (((2 * k) % r : ℕ) : ℤ) ^ (2 * p))
    (fun k => ((2 * k : ℕ) : ℤ) ^ (2 * p)
        - ((2 * p : ℤ)) * ((2 * k : ℕ) : ℤ) ^ (2 * p - 1)
          * (((r : ℤ)) * (((2 * k : ℕ) : ℤ) / ((r : ℤ)))))
    (((r : ℤ)) * ((r : ℤ))) hper
  rw [perm_two_mod r hr hr2 (fun k => ((k : ℕ) : ℤ) ^ (2 * p))] at hsum
  -- now hsum : S ≡ ∑ (a_k - b_k)
  have hsplit :
      (∑ k ∈ Finset.range r, (((2 * k : ℕ) : ℤ) ^ (2 * p)
          - ((2 * p : ℤ)) * ((2 * k : ℕ) : ℤ) ^ (2 * p - 1)
            * (((r : ℤ)) * (((2 * k : ℕ) : ℤ) / ((r : ℤ))))))
      = ((2 : ℤ)) ^ (2 * p) * (∑ k ∈ Finset.range r, ((k : ℕ) : ℤ) ^ (2 * p))
        - ((2 * p : ℤ)) * ((r : ℤ)) * T' := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      rw [mul_pow]
      try ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
  rw [hsplit] at hsum
  exact hsum

/-! ### final assembly -/

lemma dvd_of_dvd_mul_sq {p x y : ℕ} (hp : p.Prime) (hpx : ¬ p ∣ x) (h : p * p ∣ x * y) :
    p * p ∣ y := by
  have hcop : Nat.Coprime x (p * p) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨r, hr1, hr2⟩ := Nat.exists_prime_and_dvd hg
    have hxr : r ∣ x := hr2.trans (Nat.gcd_dvd_left x (p * p))
    have hrp : r ∣ p * p := hr2.trans (Nat.gcd_dvd_right x (p * p))
    rcases (Nat.Prime.dvd_mul hr1).1 hrp with h' | h'
    · rcases hp.eq_one_or_self_of_dvd r h' with h1 | h1
      · exact absurd h1 hr1.ne_one
      · exact hpx (h1 ▸ hxr)
    · rcases hp.eq_one_or_self_of_dvd r h' with h1 | h1
      · exact absurd h1 hr1.ne_one
      · exact hpx (h1 ▸ hxr)
  exact hcop.symm.dvd_of_dvd_mul_right (by rw [Nat.mul_comm y x]; exact h)

section Final

variable {p : ℕ}

/-- `p²` divides the power sum `∑_{k<p} k^{2p}`. -/
lemma S_p_dvd (hp : p.Prime) (h3 : 3 < p) :
    p * p ∣ ∑ k ∈ Finset.range p, (k ^ (2 * p)) := by
  classical
  have hp5 : 5 ≤ p := by
    have := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
    omega
  have hdoub := doubling p p hp (by omega)
  set Tval : ℤ := ∑ k ∈ Finset.range p, ((2 * k : ℕ) : ℤ) ^ (2 * p - 1)
    * (((2 * k : ℕ) : ℤ) / ((p : ℤ))) with hTval
  have hc : ((2 * p : ℤ)) * ((p : ℤ)) * Tval ≡ 0 [ZMOD ((p : ℤ)) * ((p : ℤ))] := by
    rw [Int.modEq_iff_dvd]
    have hre : ((2 * p : ℤ)) * ((p : ℤ)) * Tval = ((p : ℤ)) * ((p : ℤ)) * (2 * Tval) := by
      ring
    rw [hre]
    exact ⟨-2 * Tval, by ring⟩
  have hmain : (∑ k ∈ Finset.range p, ((k : ℕ) : ℤ) ^ (2 * p))
      ≡ ((2 : ℤ)) ^ (2 * p) * (∑ k ∈ Finset.range p, ((k : ℕ) : ℤ) ^ (2 * p))
      [ZMOD ((p : ℤ)) * ((p : ℤ))] := by
    refine hdoub.trans ?_
    refine (Int.ModEq.sub (Int.ModEq.refl _) hc).trans ?_
    rw [sub_zero]
  rw [Int.modEq_iff_dvd] at hmain
  have h0' : ((p : ℤ)) * ((p : ℤ)) ∣ (((2 : ℤ)) ^ (2 * p) - 1)
      * (∑ k ∈ Finset.range p, ((k : ℕ) : ℤ) ^ (2 * p)) := by
    have hexp : ((2 : ℤ)) ^ (2 * p)
        * (∑ k ∈ Finset.range p, ((k : ℕ) : ℤ) ^ (2 * p))
          - (∑ k ∈ Finset.range p, ((k : ℕ) : ℤ) ^ (2 * p))
        = (((2 : ℤ)) ^ (2 * p) - 1)
          * (∑ k ∈ Finset.range p, ((k : ℕ) : ℤ) ^ (2 * p)) := by ring
    rw [← hexp]
    exact hmain
  -- p does not divide 2^{2p} - 1
  have h2m := two_pow_mod p hp h3 p hp (Or.inl rfl)
  rw [Int.modEq_iff_dvd] at h2m
  have hpd : ¬ p ∣ (2 ^ (2 * p) - 1) := by
    intro hbad
    have hbadZ : ((p : ℤ)) ∣ (((2 ^ (2 * p) - 1 : ℕ)) : ℤ) := by
      exact_mod_cast hbad
    have hkey : ((2 : ℤ)) ^ (2 * p) = (((2 ^ (2 * p) : ℕ)) : ℤ) := by
      push_cast
      rfl
    rw [hkey] at h2m
    have hC : ((p : ℤ)) ∣ (((2 ^ (2 * p) - 4 : ℕ)) : ℤ) := by
      have h44 : (4 : ℕ) ≤ 2 ^ (2 * p) := by
        have h4 : (2 : ℕ) ^ 2 ≤ (2 : ℕ) ^ (2 * p) := Nat.pow_le_pow_right (n := 2) (by norm_num : (0 : ℕ) < 2) (i := 2) (j := 2 * p) (by omega)
        simpa using h4
      rw [Nat.cast_sub h44,
        show (((2 ^ (2 * p) : ℕ) : ℤ)) - ((4 : ℕ) : ℤ) = -(((4 : ℤ)) - (((2 ^ (2 * p) : ℕ) : ℤ))) from by ring]
      exact Int.dvd_neg.2 h2m
    have hh := hbadZ.sub hC
    have hrr : ((2 ^ (2 * p) - 1 : ℕ) : ℤ) - ((2 ^ (2 * p) - 4 : ℕ) : ℤ)
        = ((3 : ℕ) : ℤ) := by
      have h4 : (2 : ℕ) ^ 2 ≤ (2 : ℕ) ^ (2 * p) := Nat.pow_le_pow_right (n := 2) (by norm_num : (0 : ℕ) < 2) (i := 2) (j := 2 * p) (by omega)
      have h44 : (4 : ℕ) ≤ 2 ^ (2 * p) := by simpa using h4
      rw [← Nat.cast_sub (show 2 ^ (2 * p) - 4 ≤ 2 ^ (2 * p) - 1 by omega)]
      congr 1
      omega
    rw [hrr] at hh
    rw [Int.natCast_dvd_natCast] at hh
    have hle2 : p ≤ 3 := Nat.le_of_dvd three_pos hh
    omega
  -- transfer everything to ℕ
  have hcast : (∑ k ∈ Finset.range p, ((k : ℕ) : ℤ) ^ (2 * p))
      = ((∑ k ∈ Finset.range p, (k ^ (2 * p)) : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun k _ => by push_cast; rfl
  have hc2 : (((2 : ℤ)) ^ (2 * p) - 1) = (((2 ^ (2 * p) - 1 : ℕ)) : ℤ) := by
    have hkey : ((2 : ℤ)) ^ (2 * p) = (((2 ^ (2 * p) : ℕ)) : ℤ) := by
      push_cast
      rfl
    rw [hkey, Nat.cast_sub (Nat.one_le_two_pow : (1 : ℕ) ≤ 2 ^ (2 * p))]
    norm_num
  rw [hcast, hc2] at h0'
  have h0'' : (((p * p : ℕ)) : ℤ)
      ∣ (((2 ^ (2 * p) - 1) * (∑ k ∈ Finset.range p, k ^ (2 * p)) : ℕ) : ℤ) := by
    rw [Int.natCast_mul, Int.natCast_mul]
    exact h0'
  rw [Int.natCast_dvd_natCast] at h0''
  exact dvd_of_dvd_mul_sq hp hpd h0''

end Final

/-! ### integer division helpers -/

lemma int_div_eq_zero (a b : ℤ) (hb : 0 < b) (hnn : 0 ≤ a) (hlt : a < b) : a / b = 0 :=
  Int.ediv_eq_zero_of_lt hnn hlt

lemma int_div_eq_one (a b : ℤ) (hb : 0 < b) (hge : b ≤ a) (hlt : a < 2 * b) : a / b = 1 := by
  have hmod : a % b = a - b := by
    rw [show a % b = (a - b + b * 1) % b from by congr 1; ring,
      Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  have hd : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
  have h2 : b * (a / b) = b * 1 := by rw [mul_one]; omega
  exact mul_left_cancel₀ hb.ne' h2

/-- The correction sum at `q = 2p−1` is nonzero mod `q`. -/
lemma T_nonvanish (hp : p.Prime) (h3 : 3 < p) (hp' : (2 * p - 1).Prime) :
    ¬ (((2 * p - 1 : ℕ) : ℤ)) ∣ (∑ k ∈ Finset.range (2 * p - 1),
      ((2 * k : ℕ) : ℤ) ^ (2 * p - 1) * (((2 * k : ℕ) : ℤ) / ((2 * p - 1 : ℕ) : ℤ))) := by
  classical
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
  have hqodd : (2 * p - 1) % 2 = 1 := by omega
  have hqpos : (0 : ℤ) < ((2 * p - 1 : ℕ) : ℤ) := by
    have hq5 : 0 < 2 * p - 1 := by omega
    exact_mod_cast hq5
  have hqp : 2 * p - 1 - p = p - 1 := by omega
  set F : ℕ → ℤ := fun k =>
    ((2 * k : ℕ) : ℤ) ^ (2 * p - 1) * (((2 * k : ℕ) : ℤ) / ((2 * p - 1 : ℕ) : ℤ)) with hF
  have hunion : Finset.range (2 * p - 1) = Finset.range p ∪ Finset.Ico p (2 * p - 1) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range p) (Finset.Ico p (2 * p - 1)) := by
    rw [Finset.disjoint_right]
    intro x hx hx2
    simp only [Finset.mem_range, Finset.mem_Ico] at hx2 hx
    omega
  rw [hunion, Finset.sum_union hdisj]
  have hfirst : (∑ k ∈ Finset.range p, F k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have h1 : k < p := Finset.mem_range.1 hk
    have h2 : 2 * k < 2 * p - 1 := by omega
    have hlt : ((2 * k : ℕ) : ℤ) < ((2 * p - 1 : ℕ) : ℤ) := by exact_mod_cast h2
    have hnn : (0 : ℤ) ≤ ((2 * k : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
    have : ((2 * k : ℕ) : ℤ) / ((2 * p - 1 : ℕ) : ℤ) = 0 :=
      int_div_eq_zero _ _ hqpos hnn hlt
    simp only [hF]
    rw [this, mul_zero]
  rw [hfirst, zero_add]
  have hsecond : (∑ k ∈ Finset.Ico p (2 * p - 1), F k)
      = ∑ k ∈ Finset.Ico p (2 * p - 1), ((2 * k : ℕ) : ℤ) ^ (2 * p - 1) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hmem : p ≤ k ∧ k < 2 * p - 1 := Finset.mem_Ico.1 hk
    have hge : ((2 * p - 1 : ℕ) : ℤ) ≤ ((2 * k : ℕ) : ℤ) := by
      have h1 : 2 * p - 1 ≤ 2 * k := by omega
      exact_mod_cast h1
    have hlt : ((2 * k : ℕ) : ℤ) < 2 * ((2 * p - 1 : ℕ) : ℤ) := by
      have h1 : 2 * k < 2 * (2 * p - 1) := by omega
      exact_mod_cast h1
    have : ((2 * k : ℕ) : ℤ) / ((2 * p - 1 : ℕ) : ℤ) = 1 :=
      int_div_eq_one _ _ hqpos hge hlt
    simp only [hF]
    rw [this, mul_one]
  rw [hsecond]
  have hferm : ∀ k ∈ Finset.Ico p (2 * p - 1),
      ((2 * k : ℕ) : ℤ) ^ (2 * p - 1) ≡ ((2 * k : ℕ) : ℤ) [ZMOD ((2 * p - 1 : ℕ) : ℤ)] := by
    intro k hk
    have hmem : p ≤ k ∧ k < 2 * p - 1 := Finset.mem_Ico.1 hk
    have hne : ¬ (((2 * p - 1 : ℕ) : ℤ)) ∣ ((2 * k : ℕ) : ℤ) := by
      intro hdvd
      have hposk : (0 : ℤ) < ((2 * k : ℕ) : ℤ) := by
        have h1 : 0 < 2 * k := by omega
        exact_mod_cast h1
      have hlt : ((2 * k : ℕ) : ℤ) < 2 * ((2 * p - 1 : ℕ) : ℤ) := by
        have h1 : 2 * k < 2 * (2 * p - 1) := by omega
        exact_mod_cast h1
      obtain ⟨m, hm⟩ := hdvd
      have hm1 : m = 1 := by
        rcases Int.lt_trichotomy 1 m with h | h | h
        · have hbig : ((2 * p - 1 : ℕ) : ℤ) * 2 ≤ ((2 * p - 1 : ℕ) : ℤ) * m := by
            refine mul_le_mul_of_nonneg_left h (Int.le_of_lt hqpos)
          push_cast at hbig
          omega
        · exact h.symm
        · have hle : ((2 * p - 1 : ℕ) : ℤ) * m ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hqpos) (by omega)
          omega
      rw [hm1, mul_one] at hm
      have hke : (2 * k : ℕ) = 2 * p - 1 := by exact_mod_cast hm
      omega
    have h2 : 2 * p - 1 = ((2 * p - 1) - 1) + 1 := by omega
    rw [h2, pow_add, pow_one,
      show ((2 * p - 1 : ℕ) - 1) + 1 = 2 * p - 1 from by omega]
    have hf := fermat_zmod (2 * p - 1) hp' _ hne
    calc ((2 * k : ℕ) : ℤ) ^ ((2 * p - 1) - 1) * ((2 * k : ℕ) : ℤ)
        ≡ ((1 : ℤ)) * ((2 * k : ℕ) : ℤ) [ZMOD ((2 * p - 1 : ℕ) : ℤ)] :=
          Int.ModEq.mul hf (Int.ModEq.refl _)
      _ = ((2 * k : ℕ) : ℤ) := by ring
  have hsum2 := sum_modEq (Finset.Ico p (2 * p - 1))
    (fun k => ((2 * k : ℕ) : ℤ) ^ (2 * p - 1)) (fun k => ((2 * k : ℕ) : ℤ))
    ((2 * p - 1 : ℕ) : ℤ) hferm
  have hsumval : ∑ k ∈ Finset.Ico p (2 * p - 1), ((2 * k : ℕ) : ℤ)
      = (((p - 1) * (3 * p - 2) : ℕ) : ℤ) := by
    have hrange : ∑ k ∈ Finset.Ico p (2 * p - 1), ((2 * k : ℕ) : ℤ)
        = ∑ j ∈ Finset.range (2 * p - 1 - p), ((2 * (p + j) : ℕ) : ℤ) :=
      (Finset.sum_Ico_eq_sum_range (fun k => ((2 * k : ℕ) : ℤ)) p (2 * p - 1))
    rw [hrange, hqp]
    have hexpand : ∀ j ∈ Finset.range (p - 1),
        ((2 * (p + j) : ℕ) : ℤ) = (((2 * p : ℕ) : ℤ)) + 2 * ((j : ℕ) : ℤ) := by
      intro j _
      push_cast
      ring
    rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib, Finset.sum_const]
    simp only [Finset.card_range, nsmul_eq_mul]
    have hid : ∑ j ∈ Finset.range (p - 1), (2 * ((j : ℕ) : ℤ))
        = 2 * (((∑ j ∈ Finset.range (p - 1), j : ℕ) : ℤ)) := by
      rw [Nat.cast_sum, Finset.mul_sum]
    rw [hid, Finset.sum_range_id]
    have hd2 : 2 ∣ (p - 1) * (p - 2) := dvd_mul_of_dvd_left (by omega) (p - 2)
    have hcancel : 2 * (((p - 1) * (p - 2) / 2 : ℕ) : ℤ)
        = (((p - 1) * (p - 2) : ℕ) : ℤ) := by
      have h1 := Nat.div_mul_cancel hd2
      push_cast
      linarith
    rw [show (p - 1 - 1 : ℕ) = p - 2 from by omega, hcancel,
      show (3 * p - 2 : ℕ) = 2 * p + (p - 2) from by omega]
    simp only [Nat.cast_mul, Nat.cast_add]
    push_cast
    ring
  rw [hsumval] at hsum2
  intro hdvd
  rw [Int.modEq_iff_dvd] at hsum2
  have hsum3 : ((2 * p - 1 : ℕ) : ℤ) ∣ (((p - 1) * (3 * p - 2) : ℕ) : ℤ) := by
    have hadd := hsum2.add hdvd
    simpa using hadd
  have hsplit : (((p - 1) * (3 * p - 2) : ℕ) : ℤ)
      = ((p - 1 : ℕ) : ℤ) * ((2 * p - 1 : ℕ) : ℤ) + ((p - 1 : ℕ) : ℤ) * ((p - 1 : ℕ) : ℤ) := by
    have hsplit2 : (3 * p - 2 : ℕ) = (2 * p - 1) + (p - 1) := by omega
    rw [hsplit2, Nat.cast_mul, Nat.cast_add]
    ring
  have hmul : ((2 * p - 1 : ℕ) : ℤ) ∣ ((p - 1 : ℕ) : ℤ) * ((2 * p - 1 : ℕ) : ℤ) :=
    dvd_mul_left _ _
  rw [hsplit] at hsum3
  have hfin0 := hsum3.sub hmul
  rw [show ((p - 1 : ℕ) : ℤ) * ((2 * p - 1 : ℕ) : ℤ) + ((p - 1 : ℕ) : ℤ) * ((p - 1 : ℕ) : ℤ)
      - ((p - 1 : ℕ) : ℤ) * ((2 * p - 1 : ℕ) : ℤ)
      = ((p - 1 : ℕ) : ℤ) * ((p - 1 : ℕ) : ℤ) from by ring] at hfin0
  have hfin : ((2 * p - 1 : ℕ) : ℤ) ∣ ((p - 1 : ℕ) : ℤ) * ((p - 1 : ℕ) : ℤ) := hfin0
  have hfin2 : (2 * p - 1) ∣ (p - 1) * (p - 1) := by
    rw [← Int.natCast_mul] at hfin
    exact Int.natCast_dvd_natCast.mp hfin
  rcases (Nat.Prime.dvd_mul hp').1 hfin2 with h' | h'
  · have hle : (2 * p - 1) ≤ p - 1 := Nat.le_of_dvd (by omega) h'
    omega
  · have hle : (2 * p - 1) ≤ p - 1 := Nat.le_of_dvd (by omega) h'
    omega



/-! ### the main theorem -/

lemma modEq_of_eq' {x y n : ℤ} (h : x = y) : x ≡ y [ZMOD n] := by
  rw [Int.modEq_iff_dvd, h, sub_self]
  exact dvd_zero _

lemma intprime_dvd_mul {p : ℕ} (hp : p.Prime) {a b : ℤ} (h : ((p : ℤ)) ∣ a * b) :
    ((p : ℤ)) ∣ a ∨ ((p : ℤ)) ∣ b := by
  have hq : p ∣ a.natAbs * b.natAbs := by
    have h1 : ((p : ℤ)) ∣ ((a.natAbs * b.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_mul]
      rcases Int.natAbs_eq a with hh | hh <;>
        rcases Int.natAbs_eq b with hh2 | hh2 <;>
        rw [hh, hh2] at h <;> simpa using h
    exact Int.natCast_dvd_natCast.mp h1
  rcases Nat.Prime.dvd_mul hp |>.mp hq with h1 | h1
  · refine Or.inl ?_
    have h2 : ((p : ℤ)) ∣ ((a.natAbs : ℕ) : ℤ) := by exact_mod_cast h1
    rcases Int.natAbs_eq a with hh | hh <;> rw [hh] at h2 <;> simpa using h2
  · refine Or.inr ?_
    have h2 : ((p : ℤ)) ∣ ((b.natAbs : ℕ) : ℤ) := by exact_mod_cast h1
    rcases Int.natAbs_eq b with hh | hh <;> rw [hh] at h2 <;> simpa using h2

section MainThm

variable {p : ℕ}

lemma q_not_dvd_N (hp : p.Prime) (h3 : 3 < p) (hp' : (2 * p - 1).Prime) {N : ℤ}
    (hBN : bernoulli (2 * p) = ((N : ℤ) : ℚ) / ((6 : ℕ) : ℚ)) :
    ¬ (((2 * p - 1 : ℕ) : ℤ)) ∣ N := by
  classical
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
  have hqodd : (2 * p - 1) % 2 = 1 := by omega
  have hqpos : (0 : ℤ) < ((2 * p - 1 : ℕ) : ℤ) := by
    have hq5 : 0 < 2 * p - 1 := by omega
    exact_mod_cast hq5
  intro hdvd
  obtain ⟨z, c, hc0, hcq, hqeq⟩ := faulhaber_LD hp h3 hp' hp' (Or.inr rfl)
  have hcastQ : (∑ k ∈ Finset.range (2 * p - 1), ((k : ℕ) : ℚ) ^ (2 * p))
      = (((∑ k ∈ Finset.range (2 * p - 1), ((k : ℕ) : ℤ) ^ (2 * p)) : ℤ) : ℚ) := by
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun k _ => by push_cast; rfl
  set Sq : ℤ := ∑ k ∈ Finset.range (2 * p - 1), ((k : ℕ) : ℤ) ^ (2 * p) with hSq
  rw [hcastQ, hBN] at hqeq
  have h6 : (((6 : ℕ) : ℚ)) ≠ 0 := by norm_num
  have hcq0 : (((c : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hc0
  have hq0 : (((2 * p - 1 : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hQeq : ((Sq : ℤ) : ℚ) * ((6 : ℤ)) * ((c : ℕ) : ℚ)
      = (((2 * p - 1 : ℕ) : ℤ)) * ((N : ℤ)) * ((c : ℕ) : ℚ)
        + (((2 * p - 1 : ℕ) : ℤ)) * (((2 * p - 1 : ℕ) : ℤ)) * z * ((6 : ℤ)) := by
    have hq2 := hqeq
    field_simp at hq2 ⊢
    push_cast at hq2 ⊢
    linarith
  have hzero : (((2 * p - 1 : ℕ) : ℤ)) * (((2 * p - 1 : ℕ) : ℤ)) ∣ ((6 : ℤ)) * ((c : ℕ) : ℤ) * Sq := by
    obtain ⟨t, ht⟩ := hdvd
    have h1 : (((2 * p - 1 : ℕ) : ℤ)) * ((c : ℕ) : ℤ) * N
        = (((2 * p - 1 : ℕ) : ℤ)) * (((2 * p - 1 : ℕ) : ℤ)) * (((c : ℕ) : ℤ) * t) := by
      rw [ht]
      ring
    have h2 : (((2 * p - 1 : ℕ) : ℤ)) * (((2 * p - 1 : ℕ) : ℤ)) * z * ((6 : ℤ))
        = (((2 * p - 1 : ℕ) : ℤ)) * (((2 * p - 1 : ℕ) : ℤ)) * ((6 : ℤ) * z) := by ring
    have hleft : ((6 : ℤ)) * ((c : ℕ) : ℤ) * Sq
        = (((2 * p - 1 : ℕ) : ℤ)) * ((c : ℕ) : ℤ) * N
          + (((2 * p - 1 : ℕ) : ℤ)) * (((2 * p - 1 : ℕ) : ℤ)) * z * ((6 : ℤ)) := by
      have hQ2 := hQeq
      apply Int.cast_injective (α := ℚ)
      push_cast at hQ2 ⊢
      linear_combination hQ2
    rw [hleft, h1, h2]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_refl _) _)
      (dvd_mul_of_dvd_left (dvd_refl _) _)
  have hdoub := doubling p (2 * p - 1) hp' (by omega)
  set Tval : ℤ := ∑ k ∈ Finset.range (2 * p - 1),
    ((2 * k : ℕ) : ℤ) ^ (2 * p - 1) * (((2 * k : ℕ) : ℤ) / ((2 * p - 1 : ℕ) : ℤ)) with hTv
  have hTn : ¬ (((2 * p - 1 : ℕ) : ℤ)) ∣ Tval := hTv ▸ T_nonvanish hp h3 hp'
  have hmain : (((2 : ℤ)) ^ (2 * p) - 1) * Sq ≡
      ((2 * p : ℤ)) * (((2 * p - 1 : ℕ) : ℤ)) * Tval
      [ZMOD ((2 * p - 1 : ℕ) : ℤ) * ((2 * p - 1 : ℕ) : ℤ)] := by
    have hstep : ((2 : ℤ)) ^ (2 * p) * Sq - Sq ≡
        ((2 * p : ℤ)) * (((2 * p - 1 : ℕ) : ℤ)) * Tval
        [ZMOD ((2 * p - 1 : ℕ) : ℤ) * ((2 * p - 1 : ℕ) : ℤ)] :=
      ((Int.ModEq.refl ((((2 : ℤ)) ^ (2 * p) * Sq))).sub hdoub).trans
        (modEq_of_eq' (by
          ring))
    have keyL : (((2 : ℤ)) ^ (2 * p) - 1) * Sq
        = ((2 : ℤ)) ^ (2 * p) * Sq - Sq := by ring
    exact (modEq_of_eq' keyL).trans hstep
  have hm1 : (((2 : ℤ)) ^ (2 * p) - 1) * (((6 : ℤ)) * ((c : ℕ) : ℤ) * Sq) ≡ 0
      [ZMOD ((2 * p - 1 : ℕ) : ℤ) * ((2 * p - 1 : ℕ) : ℤ)] := by
    have keyL : (((2 : ℤ)) ^ (2 * p) - 1) * (((6 : ℤ)) * ((c : ℕ) : ℤ) * Sq)
        = ((6 : ℤ)) * ((c : ℕ) : ℤ) * Sq * (((2 : ℤ)) ^ (2 * p) - 1) := by ring
    exact (modEq_of_eq' keyL).trans
      (((Int.modEq_zero_iff_dvd.2 hzero).mul (Int.ModEq.refl _)).trans
        (modEq_of_eq' (by ring)))
  have hm2 : (((2 : ℤ)) ^ (2 * p) - 1) * (((6 : ℤ)) * ((c : ℕ) : ℤ) * Sq) ≡
      ((6 : ℤ)) * ((c : ℕ) : ℤ) * (((2 * p : ℤ)) * (((2 * p - 1 : ℕ) : ℤ)) * Tval)
      [ZMOD ((2 * p - 1 : ℕ) : ℤ) * ((2 * p - 1 : ℕ) : ℤ)] := by
    have keyL : (((2 : ℤ)) ^ (2 * p) - 1) * (((6 : ℤ)) * ((c : ℕ) : ℤ) * Sq)
        = (((2 : ℤ)) ^ (2 * p) - 1) * Sq * (((6 : ℤ)) * ((c : ℕ) : ℤ)) := by ring
    have keyR : (((2 * p : ℤ)) * (((2 * p - 1 : ℕ) : ℤ)) * Tval) * (((6 : ℤ)) * ((c : ℕ) : ℤ))
        = ((6 : ℤ)) * ((c : ℕ) : ℤ) * (((2 * p : ℤ)) * (((2 * p - 1 : ℕ) : ℤ)) * Tval) := by
      ring
    have hmid := hmain.mul (Int.ModEq.refl (((6 : ℤ)) * ((c : ℕ) : ℤ)))
    exact (modEq_of_eq' keyL).trans (hmid.trans (modEq_of_eq' keyR))
  have hfin := hm2.symm.trans hm1
  rw [Int.modEq_iff_dvd, zero_sub, Int.dvd_neg] at hfin
  -- coprimality of 6c with q
  have hq6c : ¬ ((2 * p - 1 : ℕ)) ∣ (6 * c) := by
    intro hbad
    rcases (Nat.Prime.dvd_mul hp').1 hbad with h' | h'
    · have hle : (2 * p - 1) ≤ 6 := Nat.le_of_dvd (by norm_num) h'
      omega
    · exact hcq h'
  have hfinD : ((2 * p - 1 : ℕ) : ℤ) ∣ ((6 : ℤ)) * ((c : ℕ) : ℤ) * ((2 * p : ℤ)) * Tval := by
    obtain ⟨w, hw⟩ := hfin
    have hqne : ((2 * p - 1 : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (by omega : (2 * p - 1 : ℕ) ≠ 0)
    refine ⟨w, ?_⟩
    refine mul_right_cancel₀ hqne ?_
    linear_combination hw
  have hq6cZ : ¬ ((2 * p - 1 : ℕ) : ℤ) ∣ ((6 : ℤ)) * ((c : ℕ) : ℤ) := by
    intro hbad
    have h1 : ((2 * p - 1 : ℕ) : ℤ) ∣ (((6 * c : ℕ)) : ℤ) := by
      rw [show (((6 * c : ℕ)) : ℤ) = ((6 : ℤ)) * ((c : ℕ) : ℤ) from by push_cast; ring]
      exact hbad
    exact hq6c (Int.natCast_dvd_natCast.mp h1)
  rcases intprime_dvd_mul hp' hfinD with h' | hT
  · rcases intprime_dvd_mul hp' h' with h6c | h2p
    · exact hq6cZ h6c
    · exfalso
      have h2p2 : ((2 * p : ℤ)) = (((2 * p : ℕ)) : ℤ) := by push_cast; rfl
      rw [h2p2, Int.natCast_dvd_natCast] at h2p
      rcases (Nat.Prime.dvd_mul hp').1 h2p with h3' | h3'
      · have hle : (2 * p - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) h3'
        omega
      · have hle : (2 * p - 1) ≤ p := Nat.le_of_dvd (by omega) h3'
        omega
  · exact hTn hT


/-- `p ∣ N` where `B_{2p} = N / 6`. -/
lemma p_dvd_N (hp : p.Prime) (h3 : 3 < p) (hp' : (2 * p - 1).Prime) {N : ℤ}
    (hBN : bernoulli (2 * p) = ((N : ℤ) : ℚ) / ((6 : ℕ) : ℚ)) : ((p : ℤ)) ∣ N := by
  classical
  obtain ⟨z, c, hc0, hcp, hpeq⟩ := faulhaber_LD hp h3 hp' hp (Or.inl rfl)
  have hcastP : (∑ k ∈ Finset.range p, ((k : ℕ) : ℚ) ^ (2 * p))
      = (((∑ k ∈ Finset.range p, ((k : ℕ) : ℤ) ^ (2 * p)) : ℤ) : ℚ) := by
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun k _ => by push_cast; rfl
  set Sp : ℤ := ∑ k ∈ Finset.range p, ((k : ℕ) : ℤ) ^ (2 * p) with hSp
  rw [hcastP, hBN] at hpeq
  have h6 : (((6 : ℕ) : ℚ)) ≠ 0 := by norm_num
  have hcp0 : (((c : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hc0
  have hp0 : (((p : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hQeq : ((Sp : ℤ) : ℚ) * ((6 : ℤ)) * ((c : ℕ) : ℚ)
      = ((p : ℤ)) * ((N : ℤ)) * ((c : ℕ) : ℚ)
        + ((p : ℤ)) * ((p : ℤ)) * z * ((6 : ℤ)) := by
    have hp2 := hpeq
    field_simp at hp2 ⊢
    push_cast at hp2 ⊢
    linarith
  have hleft : ((6 : ℤ)) * ((c : ℕ) : ℤ) * Sp
      = ((p : ℤ)) * ((c : ℕ) : ℤ) * N + ((p : ℤ)) * ((p : ℤ)) * z * ((6 : ℤ)) := by
    have hQ2 := hQeq
    apply Int.cast_injective (α := ℚ)
    push_cast at hQ2 ⊢
    linear_combination hQ2
  -- p^2 | Sp
  have hSpnat : Sp = (((∑ k ∈ Finset.range p, k ^ (2 * p) : ℕ) : ℤ)) := by
    rw [hSp, Nat.cast_sum]
    exact Finset.sum_congr rfl fun k _ => by push_cast; rfl
  have hdvdSp : ((p : ℤ)) * ((p : ℤ)) ∣ Sp := by
    rw [hSpnat]
    exact_mod_cast S_p_dvd hp h3
  have hdvd6 : ((p : ℤ)) * ((p : ℤ)) ∣ ((6 : ℤ)) * ((c : ℕ) : ℤ) * Sp := by
    obtain ⟨s, hs⟩ := hdvdSp
    exact ⟨((6 : ℤ)) * ((c : ℕ) : ℤ) * s, by rw [hs]; ring⟩
  have hdvdR : ((p : ℤ)) * ((p : ℤ)) ∣ ((p : ℤ)) * (((c : ℕ) : ℤ) * N) := by
    have h1 := hdvd6
    rw [hleft] at h1
    have hterm : ((p : ℤ)) * ((p : ℤ)) ∣ ((p : ℤ)) * ((p : ℤ)) * z * ((6 : ℤ)) :=
      ⟨z * ((6 : ℤ)), by ring⟩
    have h2 := h1.sub hterm
    have hnorm : ((p : ℤ)) * ((c : ℕ) : ℤ) * N + ((p : ℤ)) * ((p : ℤ)) * z * ((6 : ℤ))
        - ((p : ℤ)) * ((p : ℤ)) * z * ((6 : ℤ))
        = ((p : ℤ)) * (((c : ℕ) : ℤ) * N) := by ring
    rwa [hnorm] at h2
  obtain ⟨w, hw⟩ := hdvdR
  have hcN : ((p : ℤ)) ∣ (((c : ℕ) : ℤ) * N) := by
    refine ⟨w, ?_⟩
    have hW : ((p : ℤ)) * (((c : ℕ) : ℤ) * N) = ((p : ℤ)) * (((p : ℤ)) * w) := by
      linear_combination hw
    exact mul_left_cancel₀ (show ((p : ℤ)) ≠ 0 from by exact_mod_cast hp.ne_zero) hW
  rcases intprime_dvd_mul hp hcN with hc' | hNfinal
  · exfalso
    refine hcp (Int.natCast_dvd_natCast.mp hc')
  · exact hNfinal

end MainThm

end Swarm46969

theorem swarm_proof (p : ℕ) (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    (OeisA46969.a p / 12).Prime := by
  classical
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
  obtain ⟨N, hBN, hN2, hN3⟩ := Swarm46969.B_2p_eq hp hp' h3
  obtain ⟨N', hNN'⟩ := Swarm46969.p_dvd_N hp h3 hp' hBN
  have hqN : ¬ ((2 * p - 1 : ℕ) : ℤ) ∣ N := Swarm46969.q_not_dvd_N hp h3 hp' hBN
  -- congruence facts about N'
  have hN2' : N' % 2 = 1 := by
    have h1 : (p * N') % 2 = 1 := by rw [← hNN']; exact hN2
    have h2 : ((p : ℤ)) % 2 = 1 := by exact_mod_cast hpodd
    have h3' := Int.mul_emod p N' 2
    rw [h2, one_mul] at h3'
    omega
  have hN3' : N' % 3 ≠ 0 := by
    intro h0
    have h1 : (p * N') % 3 = 1 := by rw [← hNN']; exact hN3
    have h2 : ((p : ℤ)) % 3 = 1 ∨ ((p : ℤ)) % 3 = 2 := by
      have hlt : ((p : ℤ)) % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
      have hn0 : ((p : ℤ)) % 3 ≠ 0 := by
        intro hh
        have hd3 : ((3 : ℤ)) ∣ ((p : ℤ)) := (Int.dvd_iff_emod_eq_zero).mpr hh
        have hn : (3 : ℕ) ∣ p := Int.natCast_dvd_natCast.mp hd3
        rcases hp.eq_one_or_self_of_dvd 3 hn with h1 | h1
        · omega
        · omega
      omega
    have h3' := Int.mul_emod p N' 3
    rcases h2 with hh | hh
    · rw [hh, one_mul] at h3'
      omega
    · rw [hh] at h3'
      omega
  have hqN' : ¬ ((2 * p - 1 : ℕ) : ℤ) ∣ N' := by
    intro hbad
    refine hqN ?_
    rw [hNN']
    exact dvd_mul_of_dvd_right hbad ((p : ℤ))
  -- coprimality
  have hn2 : ¬ (2 : ℕ) ∣ N'.natAbs := by
    intro h
    have h0 : ((2 : ℤ)) ∣ ((N'.natAbs : ℤ)) := by exact_mod_cast h
    have h1 : ((2 : ℤ)) ∣ N' := by
      rcases Int.natAbs_eq N' with hh | hh
      · rw [hh]
        exact h0
      · rw [hh]
        exact Int.dvd_neg.2 h0
    have h2 : N' % ((2 : ℤ)) = 0 := (Int.dvd_iff_emod_eq_zero).mp h1
    omega
  have hn3 : ¬ (3 : ℕ) ∣ N'.natAbs := by
    intro h
    have h0 : ((3 : ℤ)) ∣ ((N'.natAbs : ℤ)) := by exact_mod_cast h
    have h1 : ((3 : ℤ)) ∣ N' := by
      rcases Int.natAbs_eq N' with hh | hh
      · rw [hh]
        exact h0
      · rw [hh]
        exact Int.dvd_neg.2 h0
    have h2 : N' % ((3 : ℤ)) = 0 := (Int.dvd_iff_emod_eq_zero).mp h1
    omega
  have hnq : ¬ (2 * p - 1) ∣ N'.natAbs := by
    intro h
    have h0 : ((2 * p - 1 : ℕ) : ℤ) ∣ ((N'.natAbs : ℤ)) := by exact_mod_cast h
    rcases Int.natAbs_eq N' with hh | hh
    · refine hqN' ?_
      rw [hh]
      exact h0
    · refine hqN' ?_
      rw [hh]
      exact Int.dvd_neg.2 h0
  have hcop := Swarm46969.coprime_12q N'.natAbs hn2 hn3 hp' hnq
  -- the denominator computation
  have hpne : (0 : ℤ) < (((12 * (2 * p - 1) : ℕ) : ℤ)) := by
    have h5 : 5 ≤ p := by
      have := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
      omega
    exact_mod_cast (by omega : (0 : ℕ) < 12 * (2 * p - 1))
  have hx : bernoulli (2 * p) / (((2 * p * (2 * p - 1) : ℕ) : ℚ))
      = (((N' : ℤ) : ℚ)) / ((((12 * (2 * p - 1) : ℕ) : ℤ)) : ℚ) := by
    rw [hBN]
    have h1 : (((2 * p * (2 * p - 1) : ℕ) : ℚ)) ≠ 0 := by
      have h5 : (0 : ℕ) < 2 * p * (2 * p - 1) := by
        have h6 : 5 ≤ p := by
          have := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
          omega
        have ha : (0 : ℕ) < 2 * p := by omega
        have hb : (0 : ℕ) < 2 * p - 1 := by omega
        exact Nat.mul_pos ha hb
      exact_mod_cast (ne_of_gt h5).symm.symm
    have h2 : ((((12 * (2 * p - 1) : ℕ) : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hpne)
    rw [hNN']
    field_simp
    push_cast
    ring
  have hden : (bernoulli (2 * p) / (((2 * p * (2 * p - 1) : ℕ) : ℚ))).den
      = 12 * (2 * p - 1) := by
    rw [hx]
    have hdd := Rat.den_div_eq_of_coprime (a := N') (b := ((12 * (2 * p - 1) : ℕ) : ℤ)) hpne hcop
    simp only [Int.cast_natCast, Int.cast_mul] at hdd
    push_cast at hdd ⊢
    exact_mod_cast hdd
  have hap : OeisA46969.a p = 12 * (2 * p - 1) := by
    have h0 : p ≠ 0 := hp.ne_zero
    simp only [OeisA46969.a, if_neg h0]
    exact hden
  rw [hap, Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 12)]
  exact hp'


