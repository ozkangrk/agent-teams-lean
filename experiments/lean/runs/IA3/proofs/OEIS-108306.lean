import FormalConjectures.OEIS.«108306»

namespace OeisA108306

open Finset

/-- The general theorem: the strongly recursive convolution sequence equals the matrix power. -/
theorem swarm_core (a b : ℕ) (n : ℕ) :
    invertSeqD a b n = (genMatrix a b ^ n) 0 0 := by
  set C : ℕ → ℕ := invertSeqC a b with hC
  set D : ℕ → ℕ := invertSeqD a b with hD
  set M : Matrix (Fin 2) (Fin 2) ℕ := genMatrix a b with hM
  have hC1 : C 1 = 1 := rfl
  have hC2 : C 2 = a := by
    have h : invertSeqC a b 2 = a * b ^ 0 := rfl
    rw [hC, h, Nat.pow_zero, Nat.mul_one]
  -- ### unfolding D
  have D0 : D 0 = 1 := by
    rw [hD, invertSeqD, Nat.strongRecOn_eq]
    simp
  have Dsucc : ∀ m, 0 < m → D m = ∑ i ∈ Finset.range m, C (m - i) * D i := by
    intro m hm
    have h0 : m ≠ 0 := by omega
    rw [hD, invertSeqD, Nat.strongRecOn_eq]
    simp only []
    rw [if_neg h0]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [dif_pos (Finset.mem_range.mp hi)]
    rfl
  have D1 : D 1 = 1 := by
    rw [Dsucc 1 (by omega), Finset.sum_range_succ, Finset.range_zero,
      Finset.sum_empty, zero_add, D0, hC1, one_mul]
  have D2 : D 2 = 1 + a := by
    rw [Dsucc 2 (by omega), Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.range_zero, Finset.sum_empty, zero_add, D0, D1, hC1, hC2, one_mul]
    omega
  -- ### C at argument ≥ 2
  have C2 : ∀ k, 2 ≤ k → C k = a * b ^ (k - 2) := by
    intro k hk
    match k, hk with
    | (k' + 2), _ => rfl
  -- ### S identity
  have Sident : ∀ j, ∑ i ∈ Finset.range (j + 1), b ^ (j - i) * D i
      = D j + b * ∑ i ∈ Finset.range j, b ^ (j - 1 - i) * D i := by
    intro j
    rw [Finset.sum_range_succ]
    have hstep : ∑ i ∈ Finset.range j, b ^ (j - i) * D i
        = b * ∑ i ∈ Finset.range j, b ^ (j - 1 - i) * D i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have h1 : j - i = (j - 1 - i) + 1 := by
        have := Finset.mem_range.mp hi; omega
      rw [h1, pow_succ]
      ring
    have hjj : j - j = 0 := Nat.sub_self j
    rw [hstep, hjj, pow_zero, one_mul]
    omega
  -- ### the inductive step identity, for any m ≥ 1
  have key : ∀ m, 0 < m → D (m + 2) + b * D m = (1 + b) * D (m + 1) + a * D m := by
    intro m hm
    have hDm2 : D (m + 2)
        = D (m + 1) + a * (∑ i ∈ Finset.range (m + 1), b ^ (m - i) * D i) := by
      rw [Dsucc (m + 2) (by omega), Finset.sum_range_succ,
        show m + 2 - (m + 1) = 1 from by omega, hC1, one_mul]
      have hCeq : ∀ i ∈ Finset.range (m + 1), C (m + 2 - i) = a * b ^ (m - i) := by
        intro i hi
        rw [C2 (m + 2 - i) (by have := Finset.mem_range.mp hi; omega),
          show m + 2 - i - 2 = m - i from by have := Finset.mem_range.mp hi; omega]
      have hsum : ∑ i ∈ Finset.range (m + 1), C (m + 2 - i) * D i
          = a * ∑ i ∈ Finset.range (m + 1), b ^ (m - i) * D i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hCeq i hi, mul_assoc]
      rw [hsum]
      omega
    have hDm1 : D (m + 1)
        = D m + a * (∑ i ∈ Finset.range m, b ^ (m - 1 - i) * D i) := by
      rw [Dsucc (m + 1) (by omega), Finset.sum_range_succ,
        show m + 1 - m = 1 from by omega, hC1, one_mul]
      have hCeq : ∀ i ∈ Finset.range m, C (m + 1 - i) = a * b ^ (m - 1 - i) := by
        intro i hi
        rw [C2 (m + 1 - i) (by have := Finset.mem_range.mp hi; omega),
          show m + 1 - i - 2 = m - 1 - i from by have := Finset.mem_range.mp hi; omega]
      have hsum : ∑ i ∈ Finset.range m, C (m + 1 - i) * D i
          = a * ∑ i ∈ Finset.range m, b ^ (m - 1 - i) * D i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hCeq i hi, mul_assoc]
      rw [hsum]
      omega
    have hS := Sident m
    -- assemble
    have e1 : (1 + b) * D (m + 1)
        = D m + a * ∑ i ∈ Finset.range m, b ^ (m - 1 - i) * D i
          + b * (D m + a * ∑ i ∈ Finset.range m, b ^ (m - 1 - i) * D i) := by
      rw [Nat.add_mul, Nat.one_mul, hDm1]
    have e2 : a * (∑ i ∈ Finset.range (m + 1), b ^ (m - i) * D i)
        = a * D m + a * (b * ∑ i ∈ Finset.range m, b ^ (m - 1 - i) * D i) := by
      rw [hS, Nat.mul_add]
    rw [hDm2, e1]
    have e3 : b * (D m + a * ∑ i ∈ Finset.range m, b ^ (m - 1 - i) * D i)
        = b * D m + b * (a * ∑ i ∈ Finset.range m, b ^ (m - 1 - i) * D i) := Nat.mul_add _ _ _
    have e4 : a * (b * ∑ i ∈ Finset.range m, b ^ (m - 1 - i) * D i)
        = b * (a * ∑ i ∈ Finset.range m, b ^ (m - 1 - i) * D i) := by ring
    rw [e2, e3, e4]
    omega
  have Drec : ∀ m, D (m + 2) + b * D m = (1 + b) * D (m + 1) + a * D m := by
    intro m
    rcases m with _ | m
    · rw [D2, D1, D0, Nat.add_mul, Nat.one_mul]
      omega
    · exact key (m + 1) (by omega)
  -- ### matrix side
  have M2 : M * M + b • (1 : Matrix (Fin 2) (Fin 2) ℕ)
      = (1 + b) • M + a • (1 : Matrix (Fin 2) (Fin 2) ℕ) := by
    funext i j
    fin_cases i
    · fin_cases j
      · show (1 * 1 + a * 1 + b * 1) = (1 + b) * 1 + a * 1
        ring
      · show (1 * a + a * b + b * 0) = (1 + b) * a + a * 0
        ring
    · fin_cases j
      · show (1 * 1 + b * 1 + b * 0) = (1 + b) * 1 + a * 0
        ring
      · show (1 * a + b * b + b * 1) = (1 + b) * b + a * 1
        ring
  have Mrec : ∀ n, ((M ^ (n + 2)) + b • (M ^ n) : Matrix (Fin 2) (Fin 2) ℕ)
      = (1 + b) • (M ^ (n + 1)) + a • (M ^ n) := by
    intro n
    have e : (M ^ (n + 2) : Matrix (Fin 2) (Fin 2) ℕ) = M * M * M ^ n := by
      rw [show n + 2 = 2 + n from Nat.add_comm n 2, pow_add, pow_two]
    calc (M ^ (n + 2)) + b • (M ^ n)
        = M * M * M ^ n + b • (1 * M ^ n) := by rw [e, Matrix.one_mul]
      _ = (M * M + b • 1) * M ^ n := by rw [Matrix.add_mul, Matrix.smul_mul]
      _ = ((1 + b) • M + a • 1) * M ^ n := by rw [M2]
      _ = (1 + b) • (M * M ^ n) + a • M ^ n := by
          rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = (1 + b) • (M ^ (n + 1)) + a • (M ^ n) := by
          rw [show M * M ^ n = M ^ (n + 1) from by rw [← pow_succ']]
  -- ### final two-step induction
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [D0]
    simp [pow_zero, Matrix.one_apply]
  | one =>
    rw [D1, pow_one, hM]
    rfl
  | more k ih1 ih2 =>
    have h1 := Drec k
    rw [ih2, ih1] at h1
    have h2 : (M ^ (k + 2)) 0 0 + b * (M ^ k) 0 0
        = (1 + b) * (M ^ (k + 1)) 0 0 + a * (M ^ k) 0 0 := by
      have h3 : ((M ^ (k + 2)) + b • (M ^ k)) 0 0
          = ((1 + b) • (M ^ (k + 1)) + a • (M ^ k)) 0 0 :=
        congrFun (congrFun (Mrec k) 0) 0
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h3
      exact h3
    omega

end OeisA108306

theorem swarm_proof (a_val b_val n : ℕ) :
    OeisA108306.invertSeqD a_val b_val n = (OeisA108306.genMatrix a_val b_val ^ n) 0 0 :=
  OeisA108306.swarm_core a_val b_val n
