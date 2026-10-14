import FormalConjectures.OEIS.«108306»
open OeisA108306
open Matrix Finset

theorem E0 (A B : ℕ) : invertSeqD A B 0 = 1 := by
  unfold invertSeqD Nat.strongRecOn
  rw [WellFounded.fix_eq, if_pos rfl]

theorem Em (A B : ℕ) (m : ℕ) (hm : 0 < m) :
    invertSeqD A B m = ∑ i ∈ Finset.range m, invertSeqC A B (m - i) * invertSeqD A B i := by
  unfold invertSeqD Nat.strongRecOn
  rw [WellFounded.fix_eq, if_neg (show ¬ m = 0 by omega)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [dif_pos (Finset.mem_range.mp hi)]

theorem stepF (A B n : ℕ) :
    (genMatrix A B ^ (n + 1)) 0 0
      = (genMatrix A B ^ n) 0 0 + A * (genMatrix A B ^ n) 1 0 := by
  have hp : genMatrix A B ^ (n + 1) = genMatrix A B * genMatrix A B ^ n := by
    rw [pow_succ']
  rw [hp, Matrix.mul_apply, Fin.sum_univ_two]
  have e00 : genMatrix A B 0 0 = 1 := rfl
  have e01 : genMatrix A B 0 1 = A := rfl
  rw [e00, e01]
  ring

theorem stepH (A B n : ℕ) :
    (genMatrix A B ^ (n + 1)) 1 0
      = (genMatrix A B ^ n) 0 0 + B * (genMatrix A B ^ n) 1 0 := by
  have hp : genMatrix A B ^ (n + 1) = genMatrix A B * genMatrix A B ^ n := by
    rw [pow_succ']
  rw [hp, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : genMatrix A B 1 0 = 1 := rfl
  have e11 : genMatrix A B 1 1 = B := rfl
  rw [e10, e11]
  ring

theorem hsum (A B n : ℕ) :
    (genMatrix A B ^ n) 1 0
      = ∑ i ∈ Finset.range n, B ^ (n - 1 - i) * (genMatrix A B ^ i) 0 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stepH, ih, Finset.sum_range_succ, show n + 1 - 1 - n = 0 from by omega, pow_zero, one_mul]
    have hconv : ∑ i ∈ Finset.range n, B ^ (n + 1 - 1 - i) * (genMatrix A B ^ i) 0 0
        = B * ∑ i ∈ Finset.range n, B ^ (n - 1 - i) * (genMatrix A B ^ i) 0 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < n := Finset.mem_range.mp hi
      rw [show n + 1 - 1 - i = (n - 1 - i) + 1 from by omega, pow_succ]
      ring
    rw [hconv]
    ring

theorem swarm_proof (a_val b_val n : ℕ) :
    invertSeqD a_val b_val n = (genMatrix a_val b_val ^ n) 0 0 := by
  induction n using Nat.strongRecOn with
  | ind m ih =>
    rcases m with _ | m'
    · rw [E0]; rfl
    · rw [Em a_val b_val (m' + 1) (by omega), Finset.sum_range_succ]
      rw [show m' + 1 - m' = 1 from by omega, invertSeqC, ih m' (by omega), one_mul]
      have hinner : ∑ i ∈ Finset.range m',
            invertSeqC a_val b_val (m' + 1 - i) * invertSeqD a_val b_val i
          = a_val * ∑ i ∈ Finset.range m',
              b_val ^ (m' - 1 - i) * (genMatrix a_val b_val ^ i) 0 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i < m' := Finset.mem_range.mp hi
        rw [ih i (by omega), show m' + 1 - i = (m' - 1 - i) + 2 from by omega, invertSeqC,
          ← mul_assoc]
      rw [hinner, ← hsum]
      have hs := stepF a_val b_val m'
      omega
