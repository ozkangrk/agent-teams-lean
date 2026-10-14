
import FormalConjectures.OEIS.«108306»

/-! Submission for OEIS-108306-conjecture -/

open Matrix Finset

theorem swarm_proof (a_val b_val n : ℕ) :
    OeisA108306.invertSeqD a_val b_val n = (OeisA108306.genMatrix a_val b_val ^ n) 0 0 := by
  set M := OeisA108306.genMatrix a_val b_val with hM
  have e00 : M 0 0 = 1 := rfl
  have e01 : M 0 1 = a_val := rfl
  have e10 : M 1 0 = 1 := rfl
  have e11 : M 1 1 = b_val := rfl
  have hstep : ∀ k, (M ^ (k + 1)) 0 0 = (M ^ k) 0 0 + (M ^ k) 0 1 ∧
      (M ^ (k + 1)) 0 1 = (M ^ k) 0 0 * a_val + (M ^ k) 0 1 * b_val := by
    intro k
    constructor
    · rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, e00, e10]; try ring
    · rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, e01, e11]; try ring
  have h01 : ∀ k, (M ^ (k + 1)) 0 1 =
      a_val * ∑ i ∈ Finset.range (k + 1), b_val ^ (k - i) * (M ^ i) 0 0 := by
    intro k
    induction k with
    | zero =>
        rw [Nat.zero_add, Finset.sum_range_one, Nat.sub_self, pow_zero, one_mul, pow_one, e01,
          pow_zero]
        simp
    | succ k ih =>
        have hs := hstep (k + 1)
        have hsplit : ∑ i ∈ Finset.range (k + 1 + 1), b_val ^ (k + 1 - i) * (M ^ i) 0 0
            = b_val * ∑ i ∈ Finset.range (k + 1), b_val ^ (k - i) * (M ^ i) 0 0
              + (M ^ (k + 1)) 0 0 := by
          rw [Finset.sum_range_succ, Finset.mul_sum]
          have h1 : b_val ^ (k + 1 - (k + 1)) = 1 := by
            rw [Nat.sub_self, pow_zero]
          rw [h1, one_mul]
          refine congrArg (fun t => t + (M ^ (k + 1)) 0 0) ?_
          refine Finset.sum_congr rfl fun i hi => ?_
          have hik : i < k + 1 := Finset.mem_range.mp hi
          rw [show k + 1 - i = (k - i) + 1 from by omega, pow_succ]
          ring
        rw [hs.2, ih, hsplit]
        ring
  have hmaster : ∀ m, 1 ≤ m → (M ^ m) 0 0 =
      ∑ i ∈ Finset.range m, OeisA108306.invertSeqC a_val b_val (m - i) * (M ^ i) 0 0 := by
    intro m hm
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    match j with
    | 0 =>
        rw [Finset.sum_range_one]
        show (M ^ 1) 0 0 = OeisA108306.invertSeqC a_val b_val (1 - 0) * (M ^ 0) 0 0
        rw [pow_one, e00, pow_zero]
        rfl
    | j + 1 =>
        have hs := hstep (j + 1)
        have hj := h01 j
        have h1 : ∑ i ∈ Finset.range (j + 1), OeisA108306.invertSeqC a_val b_val (j + 1 + 1 - i)
              * (M ^ i) 0 0
            = ∑ i ∈ Finset.range (j + 1), a_val * (b_val ^ (j - i) * (M ^ i) 0 0) :=
          Finset.sum_congr rfl (fun i hi => by
            have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
            rw [show j + 1 + 1 - i = (j - i) + 2 from by omega]
            show a_val * b_val ^ (j - i) * (M ^ i) 0 0 = a_val * (b_val ^ (j - i) * (M ^ i) 0 0)
            ring)
        have hh : ∑ i ∈ Finset.range (j + 1), OeisA108306.invertSeqC a_val b_val (j + 1 + 1 - i)
              * (M ^ i) 0 0
            = a_val * ∑ i ∈ Finset.range (j + 1), b_val ^ (j - i) * (M ^ i) 0 0 := by
          rw [h1, Finset.mul_sum]
        have hc1 : OeisA108306.invertSeqC a_val b_val (j + 1 + 1 - (j + 1)) = 1 := by
          rw [show j + 1 + 1 - (j + 1) = 1 from by omega]
          rfl
        rw [Finset.sum_range_succ, hh, hc1, one_mul, hs.1, hj, Nat.add_comm]
  have D_eq : ∀ m, OeisA108306.invertSeqD a_val b_val m = if m = 0 then 1 else
      ∑ i ∈ Finset.range m, OeisA108306.invertSeqC a_val b_val (m - i)
        * OeisA108306.invertSeqD a_val b_val i := by
    intro m
    rw [show OeisA108306.invertSeqD a_val b_val m = Nat.strongRecOn m (fun m ih =>
        if m = 0 then 1
        else ∑ i ∈ Finset.range m,
          if h : i < m then OeisA108306.invertSeqC a_val b_val (m - i) * ih i h else 0) from rfl,
      Nat.strongRecOn_eq]
    by_cases hm : m = 0
    · subst hm
      simp only [if_pos]
    · simp only [if_neg hm]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [dif_pos (Finset.mem_range.mp hi)]
      rfl
  induction n using Nat.strongRecOn with
  | ind m ih =>
    rw [D_eq m]
    by_cases hm : m = 0
    · subst hm
      simp
    · simp only [if_neg hm]
      rw [Finset.sum_congr rfl fun i hi => by rw [ih i (Finset.mem_range.mp hi)]]
      exact (hmaster m (Nat.pos_of_ne_zero hm)).symm
