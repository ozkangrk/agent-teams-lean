import FormalConjectures.OEIS.«102371»

/-! Submission for OEIS-102371-conjecture -/

open Nat Finset
open OeisA102371

/- ## Bit lemmas for XOR -/

theorem xor_bit_ff (x y : ℕ) :
    Nat.bit false x ^^^ Nat.bit false y = Nat.bit false (x ^^^ y) := by rw [Nat.xor_bit]; rfl

theorem xor_bit_ft (x y : ℕ) :
    Nat.bit false x ^^^ Nat.bit true y = Nat.bit true (x ^^^ y) := by rw [Nat.xor_bit]; rfl

theorem xor_bit_tf (x y : ℕ) :
    Nat.bit true x ^^^ Nat.bit false y = Nat.bit true (x ^^^ y) := by rw [Nat.xor_bit]; rfl

theorem xor_bit_tt (x y : ℕ) :
    Nat.bit true x ^^^ Nat.bit true y = Nat.bit false (x ^^^ y) := by rw [Nat.xor_bit]; rfl

/-- XOR with an all-ones mask is truncating subtraction. -/
theorem xor_sub (n u : ℕ) (h : u < 2 ^ n) : (2 ^ n - 1) ^^^ u = 2 ^ n - 1 - u := by
  induction n generalizing u with
  | zero =>
    have h0 : u = 0 := by omega
    subst h0
    simp
  | succ n ih =>
    have hd := Nat.div_add_mod u 2
    rw [two_pow_succ] at h
    have hp : 0 < 2 ^ n := Nat.two_pow_pos n
    have hM : 2 ^ (n + 1) - 1 = Nat.bit true (2 ^ n - 1) := by
      simp only [Nat.bit_val, Bool.toNat_true]
      rw [two_pow_succ]
      omega
    rcases Nat.mod_two_eq_zero_or_one u with h0 | h0
    · obtain ⟨w, rfl⟩ : ∃ w, u = 2 * w := ⟨u / 2, by omega⟩
      have hw1 : 2 * w = Nat.bit false w := by simp [Nat.bit_val]
      rw [hM, hw1, xor_bit_tf, ih w (by omega)]
      simp only [Nat.bit_val, Bool.toNat_true, Bool.toNat_false]
      omega
    · obtain ⟨w, rfl⟩ : ∃ w, u = 2 * w + 1 := ⟨u / 2, by omega⟩
      have hw1 : 2 * w + 1 = Nat.bit true w := by simp [Nat.bit_val]
      rw [hM, hw1, xor_bit_tt, ih w (by omega)]
      simp only [Nat.bit_val, Bool.toNat_true, Bool.toNat_false]
      omega

/-- XOR with a number having a single high bit set splits off that bit. -/
theorem xor_add_pow (n v x : ℕ) (hv : v < 2 ^ n) (hx : x < 2 ^ n) :
    (2 ^ n + v) ^^^ x = 2 ^ n + (v ^^^ x) := by
  induction n generalizing v x with
  | zero =>
    have h1 : v = 0 := by omega
    subst h1
    have h2 : x = 0 := by omega
    subst h2
    simp
  | succ n ih =>
    have hdv := Nat.div_add_mod v 2
    have hdx := Nat.div_add_mod x 2
    rw [two_pow_succ] at hv hx
    have hp : 0 < 2 ^ n := Nat.two_pow_pos n
    rcases Nat.mod_two_eq_zero_or_one v with hv0 | hv0
    · obtain ⟨w, rfl⟩ : ∃ w, v = 2 * w := ⟨v / 2, by omega⟩
      have hL : 2 ^ (n + 1) + 2 * w = Nat.bit false (2 ^ n + w) := by
        simp only [Nat.bit_val, Bool.toNat_false]
        rw [two_pow_succ]
        omega
      have hw1 : 2 * w = Nat.bit false w := by simp [Nat.bit_val]
      rcases Nat.mod_two_eq_zero_or_one x with hx0 | hx0
      · obtain ⟨z, rfl⟩ : ∃ z, x = 2 * z := ⟨x / 2, by omega⟩
        have hz1 : 2 * z = Nat.bit false z := by simp [Nat.bit_val]
        rw [hL, hw1, hz1]; simp only [xor_bit_ff]; rw [ih w z (by omega) (by omega)]
        simp only [Nat.bit_val, Bool.toNat_false]
        rw [two_pow_succ]
        omega
      · obtain ⟨z, rfl⟩ : ∃ z, x = 2 * z + 1 := ⟨x / 2, by omega⟩
        have hz1 : 2 * z + 1 = Nat.bit true z := by simp [Nat.bit_val]
        rw [hL, hw1, hz1]; simp only [xor_bit_ft]; rw [ih w z (by omega) (by omega)]
        simp only [Nat.bit_val, Bool.toNat_true]
        rw [two_pow_succ]
        omega
    · obtain ⟨w, rfl⟩ : ∃ w, v = 2 * w + 1 := ⟨v / 2, by omega⟩
      have hL : 2 ^ (n + 1) + (2 * w + 1) = Nat.bit true (2 ^ n + w) := by
        simp only [Nat.bit_val, Bool.toNat_true]
        rw [two_pow_succ]
        omega
      have hw1 : 2 * w + 1 = Nat.bit true w := by simp [Nat.bit_val]
      rcases Nat.mod_two_eq_zero_or_one x with hx0 | hx0
      · obtain ⟨z, rfl⟩ : ∃ z, x = 2 * z := ⟨x / 2, by omega⟩
        have hz1 : 2 * z = Nat.bit false z := by simp [Nat.bit_val]
        rw [hL, hw1, hz1]; simp only [xor_bit_tf]; rw [ih w z (by omega) (by omega)]
        simp only [Nat.bit_val, Bool.toNat_true]
        rw [two_pow_succ]
        omega
      · obtain ⟨z, rfl⟩ : ∃ z, x = 2 * z + 1 := ⟨x / 2, by omega⟩
        have hz1 : 2 * z + 1 = Nat.bit true z := by simp [Nat.bit_val]
        rw [hL, hw1, hz1]; simp only [xor_bit_tt]; rw [ih w z (by omega) (by omega)]
        simp only [Nat.bit_val, Bool.toNat_false]
        rw [two_pow_succ]
        omega

theorem a_succ_succ (n : ℕ) :
    a (n + 2) = a (n + 1) ^^^ (a (n + 1) + (n + 2)) := by
  simp [OeisA102371.a]

theorem a_one : a 1 = 1 := rfl

/-! ## The subtracted sum of `OeisA105033` -/

def D (n : ℕ) : ℕ :=
  (Finset.range n).sum (fun k => if 2 ^ (k + 1) <= n ∧ n % 2 ^ (k + 1) = k then 2 ^ (k + 1) else 0)

theorem a105033_eq (n : ℕ) : OeisA105033.a n = n - D n := rfl

theorem D_zero : D 0 = 0 := rfl

theorem a105033_zero : OeisA105033.a 0 = 0 := rfl

theorem a105033_one : OeisA105033.a 1 = 1 := rfl

/-- If `m % q = k < m` then `q ≤ m`. -/
theorem mod_eq_lt_le (q m k : ℕ) (hkm : k < m) (hme : m % q = k) : q ≤ m := by
  rcases Nat.lt_or_ge m q with h | h
  · rw [Nat.mod_eq_of_lt h] at hme
    omega
  · omega

/-- Summing over `range (m + d + 1)` reduces to `range (m + 1)` when all intermediate terms vanish. -/
theorem sum_gap (d m : ℕ) (g : ℕ → ℕ) (h : ∀ k, m < k → k ≤ m + d → g k = 0) :
    (Finset.range (m + d + 1)).sum g = (Finset.range (m + 1)).sum g := by
  induction d generalizing m with
  | zero => simp
  | succ d ih =>
    have hs := Finset.sum_range_succ g (m + d + 1)
    have hLast := h (m + d + 1) (by omega) (by omega)
    rw [show m + (d + 1) + 1 = m + d + 1 + 1 from by omega, hs,
      ih m (fun k hk1 hk2 => h k hk1 (by omega)), hLast]
    simp

theorem pow_split (k L : ℕ) (h : k + 1 ≤ L) : ∃ c, 2 ^ L = 2 ^ (k + 1) * c := by
  refine ⟨2 ^ (L - k - 1), ?_⟩
  rw [← Nat.pow_add]
  congr 1
  omega

theorem D_strip (L m : ℕ) (hm : m < 2 ^ L) :
    D (2 ^ L + m) = D m + (if m < L then 2 ^ (m + 1) else 0) := by
  have hmn : m < 2 ^ L + m := by omega
  -- pointwise facts about the summands
  have hpt1 : ∀ k ∈ Finset.range m,
      (if 2 ^ (k + 1) <= 2 ^ L + m ∧ (2 ^ L + m) % 2 ^ (k + 1) = k then 2 ^ (k + 1) else 0)
        = (if 2 ^ (k + 1) <= m ∧ m % 2 ^ (k + 1) = k then 2 ^ (k + 1) else 0) := by
    intro k hk
    have hkm : k < m := Finset.mem_range.mp hk
    by_cases hkle : k + 1 ≤ L
    · obtain ⟨c, hc⟩ := pow_split k L hkle
      have hmod : (2 ^ L + m) % 2 ^ (k + 1) = m % 2 ^ (k + 1) := by
        rw [Nat.add_comm, hc]
        exact Nat.add_mul_mod_self_left m (2 ^ (k + 1)) c
      by_cases hfire : 2 ^ (k + 1) <= m ∧ m % 2 ^ (k + 1) = k
      · have ⟨hg, hme⟩ := hfire
        have hn1 : 2 ^ (k + 1) <= 2 ^ L + m ∧ (2 ^ L + m) % 2 ^ (k + 1) = k :=
          ⟨by omega, by rw [hmod]; exact hme⟩
        rw [if_pos hn1, if_pos hfire]
      · by_cases hfire2 : 2 ^ (k + 1) <= 2 ^ L + m ∧ (2 ^ L + m) % 2 ^ (k + 1) = k
        · obtain ⟨_, hne⟩ := hfire2
          have hme : m % 2 ^ (k + 1) = k := by rw [← hmod]; exact hne
          exact absurd (⟨mod_eq_lt_le (2 ^ (k + 1)) m k hkm hme, hme⟩ :
            2 ^ (k + 1) <= m ∧ m % 2 ^ (k + 1) = k) hfire
        · rw [if_neg hfire2, if_neg hfire]
    · -- L ≤ k: both residues are the numbers themselves, ≠ k
      have hle : 2 ^ (L + 1) ≤ 2 ^ (k + 1) :=
        Nat.pow_le_pow_right (by omega : (2:Nat) > 0) (by omega)
      rw [two_pow_succ] at hle
      have hmodn : (2 ^ L + m) % 2 ^ (k + 1) = 2 ^ L + m := Nat.mod_eq_of_lt (by omega)
      have hmodm : m % 2 ^ (k + 1) = m := Nat.mod_eq_of_lt (by omega)
      rw [hmodn, hmodm]
      have hne1 : ¬ (2 ^ (k + 1) <= 2 ^ L + m ∧ 2 ^ L + m = k) := by
        intro hc; obtain ⟨_, hq⟩ := hc; omega
      have hne2 : ¬ (2 ^ (k + 1) <= m ∧ m = k) := by
        intro hc; obtain ⟨_, hq⟩ := hc; omega
      rw [if_neg hne1, if_neg hne2]
  have hpt2 : ∀ k, m < k → k < 2 ^ L + m →
      (if 2 ^ (k + 1) <= 2 ^ L + m ∧ (2 ^ L + m) % 2 ^ (k + 1) = k then 2 ^ (k + 1) else 0) = 0 := by
    intro k hkm hkn
    by_cases hguard : 2 ^ (k + 1) <= 2 ^ L + m
    · by_cases hmod : (2 ^ L + m) % 2 ^ (k + 1) = k
      · by_cases hkl : k < L
        · obtain ⟨c, hc⟩ := pow_split k L (by omega)
          have hmod' : (2 ^ L + m) % 2 ^ (k + 1) = m % 2 ^ (k + 1) := by
            rw [Nat.add_comm, hc]
            exact Nat.add_mul_mod_self_left m (2 ^ (k + 1)) c
          rw [hmod'] at hmod
          have hle : m % 2 ^ (k + 1) ≤ m := Nat.mod_le m (2 ^ (k + 1))
          exact absurd hmod (by omega)
        · have hq2 : 2 ^ L ≤ 2 ^ (k + 1) :=
            Nat.pow_le_pow_right (by omega : (2:Nat) > 0) (by omega)
          have hc := Nat.div_add_mod (2 ^ L + m) (2 ^ (k + 1))
          rw [hmod] at hc
          obtain ⟨t, ht⟩ : ∃ t, t = 2 ^ (k + 1) * ((2 ^ L + m) / 2 ^ (k + 1)) := ⟨_, rfl⟩
          rw [← ht] at hc
          have hd1 : 1 ≤ (2 ^ L + m) / 2 ^ (k + 1) := by
            have := Nat.div_pos hguard (Nat.two_pow_pos (k + 1))
            omega
          have h1 : 2 ^ (k + 1) ≤ t := by
            rw [ht]; exact Nat.le_mul_of_pos_right _ hd1
          exact absurd hmod (by omega)
      · rw [if_neg (by intro hc; exact absurd hc.2 hmod)]
    · rw [if_neg (by intro hc; exact absurd hc.1 hguard)]
  have hptm : (if 2 ^ (m + 1) <= 2 ^ L + m ∧ (2 ^ L + m) % 2 ^ (m + 1) = m then 2 ^ (m + 1) else 0)
      = (if m < L then 2 ^ (m + 1) else 0) := by
    by_cases hml : m < L
    · obtain ⟨c, hc⟩ := pow_split m L (by omega)
      have hmlt : m < 2 ^ (m + 1) := by
        have h1 : m < 2 ^ m := Nat.lt_two_pow_self
        have h2 : 2 ^ m ≤ 2 ^ (m + 1) :=
          Nat.pow_le_pow_right (by omega : (2:Nat) > 0) (by omega)
        omega
      have hmod : (2 ^ L + m) % 2 ^ (m + 1) = m := by
        rw [Nat.add_comm, hc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmlt]
      have hguard : 2 ^ (m + 1) <= 2 ^ L + m := by
        have h1 : 2 ^ (m + 1) <= 2 ^ L :=
          Nat.pow_le_pow_right (by omega : (2:Nat) > 0) (by omega)
        omega
      rw [if_pos ⟨hguard, hmod⟩, if_pos hml]
    · have h1 : 2 ^ L ≤ 2 ^ m := Nat.pow_le_pow_right (by omega : (2:Nat) > 0) (by omega)
      have h2 : m < 2 ^ m := Nat.lt_two_pow_self
      have hlt : 2 ^ L + m < 2 ^ (m + 1) := by rw [two_pow_succ]; omega
      rw [if_neg (by omega : ¬ (2 ^ (m + 1) <= 2 ^ L + m ∧ (2 ^ L + m) % 2 ^ (m + 1) = m)),
        if_neg (by omega : ¬ (m < L))]
  -- assemble
  simp only [D]
  have hgap2 : (Finset.range (2 ^ L + m)).sum
      (fun k => if 2 ^ (k + 1) <= 2 ^ L + m ∧ (2 ^ L + m) % 2 ^ (k + 1) = k then 2 ^ (k + 1) else 0)
      = (Finset.range (m + 1)).sum
      (fun k => if 2 ^ (k + 1) <= 2 ^ L + m ∧ (2 ^ L + m) % 2 ^ (k + 1) = k then 2 ^ (k + 1) else 0) := by
    have h := sum_gap (2 ^ L + m - m - 1) m
      (fun k => if 2 ^ (k + 1) <= 2 ^ L + m ∧ (2 ^ L + m) % 2 ^ (k + 1) = k then 2 ^ (k + 1) else 0)
      (fun k hk1 hk2 => hpt2 k hk1 (by omega))
    rw [show m + (2 ^ L + m - m - 1) + 1 = 2 ^ L + m from by omega] at h
    exact h
  rw [hgap2, Finset.sum_range_succ, hptm, Finset.sum_congr rfl hpt1]

/-- The subtracted sum never exceeds `m`. -/
theorem D_le_bound : ∀ (L m : ℕ), m < 2 ^ L → D m ≤ m := by
  intro L
  induction L with
  | zero =>
    intro m hm
    have h0 : m = 0 := by omega
    subst h0
    exact D_zero.le
  | succ L ih =>
    intro m hm
    rw [two_pow_succ] at hm
    rcases Nat.lt_or_ge m (2 ^ L) with h | h
    · exact ih m h
    · obtain ⟨m', hm2⟩ : ∃ m', m = 2 ^ L + m' := ⟨m - 2 ^ L, by omega⟩
      subst hm2
      have hstrip := D_strip L m' (by omega)
      by_cases hml : m' < L
      · have h1 : 2 ^ (m' + 1) ≤ 2 ^ L :=
          Nat.pow_le_pow_right (by omega : (2:Nat) > 0) (by omega)
        have h2 := ih m' (by omega)
        rw [hstrip, if_pos hml]
        omega
      · have h2 := ih m' (by omega)
        rw [hstrip, if_neg hml]
        omega

theorem a105033_add (m : ℕ) : OeisA105033.a m + D m = m := by
  have hlt : m < 2 ^ (m + 1) := by
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    have h2 : 2 ^ m ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by omega : (2:Nat) > 0) (by omega)
    omega
  have h2 := D_le_bound (m + 1) m hlt
  rw [a105033_eq]
  omega

theorem a105033_le (m : ℕ) : OeisA105033.a m ≤ m := by
  have := a105033_add m
  omega

/-- Strip lemma for `OeisA105033.a`. -/
theorem a105033_strip (L m : ℕ) (hm : m < 2 ^ L) :
    OeisA105033.a (2 ^ L + m) = 2 ^ L + OeisA105033.a m - (if m < L then 2 ^ (m + 1) else 0) := by
  have hstrip := D_strip L m hm
  have hadd := a105033_add m
  by_cases hml : m < L
  · have h1 : 2 ^ (m + 1) ≤ 2 ^ L :=
      Nat.pow_le_pow_right (by omega : (2:Nat) > 0) (by omega)
    rw [a105033_eq, a105033_eq, hstrip, if_pos hml]
    omega
  · rw [a105033_eq, a105033_eq, hstrip, if_neg hml]
    omega

/-- `OeisA105033.a (2^L - 1) = 2^L - 1`. -/
theorem a105033_all_ones (L : ℕ) : OeisA105033.a (2 ^ L - 1) = 2 ^ L - 1 := by
  induction L with
  | zero => exact a105033_zero
  | succ L ih =>
    have hlt : 0 < 2 ^ L := Nat.two_pow_pos L
    have hlt2 : L < 2 ^ L := Nat.lt_two_pow_self
    have hstrip := a105033_strip L (2 ^ L - 1) (by omega)
    have hexp : 2 ^ (L + 1) - 1 = 2 ^ L + (2 ^ L - 1) := by rw [two_pow_succ]; omega
    rw [hexp, hstrip, if_neg (by omega : ¬ (2 ^ L - 1 < L)), ih]
    omega


/-- The XOR recurrence for `OeisA105033`. -/
theorem a105033_rec : ∀ (L n : ℕ), n < 2 ^ (L + 1) → 0 < n →
    OeisA105033.a n = OeisA105033.a (n - 1) ^^^ (n - OeisA105033.a (n - 1)) := by
  intro L
  induction L with
  | zero =>
    intro n hn hpos
    have hn1 : n = 1 := by omega
    subst hn1
    rfl
  | succ L ih =>
    intro n hn hpos
    rw [two_pow_succ] at hn
    rcases Nat.lt_or_ge n (2 ^ (L + 1)) with h | h
    · exact ih n h hpos
    · obtain ⟨m, hm2⟩ : ∃ m, n = 2 ^ (L + 1) + m := ⟨n - 2 ^ (L + 1), by omega⟩
      rw [hm2]
      have hmlt : m < 2 ^ (L + 1) := by omega
      have hposL : 0 < 2 ^ (L + 1) := Nat.two_pow_pos _
      have hAle1 := a105033_le (m - 1)
      have hAle := a105033_le m
      have hAlt : OeisA105033.a (m - 1) < 2 ^ m := by
        have h2 := Nat.lt_two_pow_self (n := m)
        omega
      have hAmt : OeisA105033.a m < 2 ^ m := by
        have h2 := Nat.lt_two_pow_self (n := m)
        omega
      have hBlt : m - OeisA105033.a (m - 1) < 2 ^ m := by
        have h2 := Nat.lt_two_pow_self (n := m)
        omega
      by_cases hm : m = 0
      · -- n = 2 ^ (L + 1)
        rw [show 2 ^ (L + 1) + m = 2 ^ (L + 1) from by omega]
        have hones := a105033_all_ones (L + 1)
        have hstrip := a105033_strip (L + 1) 0 (by omega)
        rw [if_pos (by omega : 0 < L + 1), a105033_zero,
          show 2 ^ (L + 1) + 0 = 2 ^ (L + 1) from by omega] at hstrip
        have h2b : (2:Nat) ^ 1 ≤ 2 ^ (L + 1) :=
          Nat.pow_le_pow_right (by omega : (2:Nat) > 0) (by omega)
        rw [hstrip, hones, show 2 ^ (L + 1) - (2 ^ (L + 1) - 1) = 1 from by omega,
          xor_sub (L + 1) 1 (by omega)]
        omega
      · have hm1 : 1 ≤ m := by omega
        have hih := ih m (by omega) (by omega)
        have hnm1 : 2 ^ (L + 1) + m - 1 = 2 ^ (L + 1) + (m - 1) := by omega
        have hstrip := a105033_strip (L + 1) m hmlt
        have hstrip1 := a105033_strip (L + 1) (m - 1) (by omega)
        by_cases hcase : m ≤ L
        · -- 1 ≤ m ≤ L
          rw [if_pos (by omega : m < L + 1)] at hstrip
          rw [if_pos (by omega : m - 1 < L + 1),
            show (m - 1) + 1 = m from by omega] at hstrip1
          have hz1 : 2 ^ (m + 1) ≤ 2 ^ (L + 1) :=
            Nat.pow_le_pow_right (by omega : (2:Nat) > 0) (by omega)
          have hz2 : 2 ^ m ≤ 2 ^ (L + 1) :=
            Nat.pow_le_pow_right (by omega : (2:Nat) > 0) (by omega)
          have hzz : 2 ^ m + 2 ^ m = 2 ^ (m + 1) := (two_pow_succ m).symm
          have hXc : 2 ^ (L + 1) + OeisA105033.a (m - 1) - 2 ^ m
              = (2 ^ (L + 1) - 1) ^^^ (2 ^ m - 1 - OeisA105033.a (m - 1)) := by
            rw [xor_sub (L + 1) (2 ^ m - 1 - OeisA105033.a (m - 1)) (by omega)]
            omega
          have hUc : 2 ^ m - 1 - OeisA105033.a (m - 1)
              = (2 ^ m - 1) ^^^ OeisA105033.a (m - 1) := (xor_sub m _ hAlt).symm
          have h3 : ((2 ^ m - 1) ^^^ OeisA105033.a (m - 1))
                ^^^ (2 ^ m + (m - OeisA105033.a (m - 1)))
              = 2 ^ m + ((2 ^ m - 1) ^^^ (OeisA105033.a (m - 1) ^^^ (m - OeisA105033.a (m - 1)))) := by
            rw [Nat.xor_comm, xor_add_pow m _ _ hBlt (by rw [xor_sub m _ hAlt]; omega),
              Nat.xor_comm, Nat.xor_assoc]
          have hnA : 2 ^ (L + 1) + m - (2 ^ (L + 1) + OeisA105033.a (m - 1) - 2 ^ m)
              = 2 ^ m + (m - OeisA105033.a (m - 1)) := by omega
          rw [hnm1, hstrip1, hnA, hXc, hUc, hstrip, Nat.xor_assoc, h3, ← hih,
            xor_sub m _ hAmt, xor_sub (L + 1) _ (by omega)]
          omega
        · by_cases hmb : m ≤ L + 1
          · -- m = L + 1
            have hmw : m < 2 ^ (L + 1) := by
              have h1 := Nat.lt_two_pow_self (n := L + 1)
              omega
            have hwz : 2 ^ m = 2 ^ (L + 1) := by rw [show m = L + 1 from by omega]
            rw [if_neg (by omega : ¬ (m < L + 1))] at hstrip
            rw [if_pos (by omega : m - 1 < L + 1),
              show (m - 1) + 1 = m from by omega] at hstrip1
            rw [hwz, Nat.add_sub_cancel_left] at hstrip1
            have hnA : 2 ^ (L + 1) + m - OeisA105033.a (m - 1)
                = 2 ^ (L + 1) + (m - OeisA105033.a (m - 1)) := by omega
            rw [hnm1, hstrip1, hnA, hstrip,
              Nat.xor_comm (OeisA105033.a (m - 1)) (2 ^ (L + 1) + (m - OeisA105033.a (m - 1))),
              xor_add_pow (L + 1) (m - OeisA105033.a (m - 1)) (OeisA105033.a (m - 1))
                (by omega) (by omega),
              Nat.xor_comm (m - OeisA105033.a (m - 1)) (OeisA105033.a (m - 1)),
              ← hih]
            omega
          · -- m ≥ L + 2
            rw [if_neg (by omega : ¬ (m < L + 1)), Nat.sub_zero] at hstrip
            rw [if_neg (by omega : ¬ (m - 1 < L + 1)), Nat.sub_zero] at hstrip1
            have hnA : 2 ^ (L + 1) + m - (2 ^ (L + 1) + OeisA105033.a (m - 1))
                = m - OeisA105033.a (m - 1) := by omega
            rw [hnm1, hstrip1, hnA, hstrip,
              xor_add_pow (L + 1) (OeisA105033.a (m - 1)) (m - OeisA105033.a (m - 1))
                (by omega) (by omega),
              ← hih]

theorem a105033_rec' (n : ℕ) (hn : 0 < n) :
    OeisA105033.a n = OeisA105033.a (n - 1) ^^^ (n - OeisA105033.a (n - 1)) := by
  have hlt : n < 2 ^ (n + 1) := by
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : 2 ^ n ≤ 2 ^ (n + 1) :=
      Nat.pow_le_pow_right (by omega : (2:Nat) > 0) (by omega)
    omega
  exact a105033_rec n n hlt hn

/- ## Main theorem -/

theorem main_sum : ∀ n : ℕ, 0 < n → a n + OeisA105033.a (n - 1) = 2 ^ n - 1 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn1
    by_cases hn0 : n = 0
    · subst hn0
      simp [a_one, a105033_zero]
    · have hnpos : 0 < n := by omega
      have hih := ih hnpos
      have hT1 := a105033_le (n - 1)
      have hA1 : OeisA105033.a (n - 1) < 2 ^ n := by
        have h1 := a105033_le (n - 1)
        have h2 : n < 2 ^ n := Nat.lt_two_pow_self
        omega
      have hAn : OeisA105033.a n < 2 ^ n := by
        have h1 := a105033_le n
        have h2 : n < 2 ^ n := Nat.lt_two_pow_self
        omega
      have hv2 : n - OeisA105033.a (n - 1) < 2 ^ n := by
        have h2 : n < 2 ^ n := Nat.lt_two_pow_self
        omega
      have han : a n = 2 ^ n - 1 - OeisA105033.a (n - 1) := by omega
      have hstep : a (n + 1) = a n ^^^ (a n + (n + 1)) := by
        have hs := a_succ_succ (n - 1)
        rw [show n - 1 + 1 = n from by omega,
          show n - 1 + 2 = n + 1 from by omega] at hs
        exact hs
      have hv : a n + (n + 1) = 2 ^ n + (n - OeisA105033.a (n - 1)) := by omega
      have hrec := a105033_rec' n hnpos
      rw [show (n + 1) - 1 = n from by omega, hstep, hv, han,
        show 2 ^ n - 1 - OeisA105033.a (n - 1) = (2 ^ n - 1) ^^^ OeisA105033.a (n - 1) from
          (xor_sub n _ hA1).symm]
      rw [Nat.xor_comm ((2 ^ n - 1) ^^^ OeisA105033.a (n - 1)) (2 ^ n + (n - OeisA105033.a (n - 1))),
        xor_add_pow n (n - OeisA105033.a (n - 1)) ((2 ^ n - 1) ^^^ OeisA105033.a (n - 1)) hv2
          (by rw [xor_sub n _ hA1]; omega),
        Nat.xor_comm (n - OeisA105033.a (n - 1)) ((2 ^ n - 1) ^^^ OeisA105033.a (n - 1)),
        Nat.xor_assoc, ← hrec, xor_sub n _ hAn, two_pow_succ]
      omega

theorem swarm_proof : answer(True) ↔ ∀ n : ℕ, 0 < n → a n = 2 ^ n - 1 - OeisA105033.a (n - 1) := by
  constructor
  · intro _ n hn
    have := main_sum n hn
    omega
  · intro _
    trivial
