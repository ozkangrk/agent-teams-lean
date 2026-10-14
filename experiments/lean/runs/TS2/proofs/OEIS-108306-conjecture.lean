
import FormalConjectures.OEIS.«108306»

open OeisA108306
open Matrix

theorem C_succ (a b : Nat) : (j : Nat) -> 2 <= j -> invertSeqC a b (j+1) = b * invertSeqC a b j
  | 0, h => by omega
  | 1, h => by omega
  | (m+2), h => by
      have e1 : invertSeqC a b (m+3) = a * b^(m+1) := rfl
      have e2 : invertSeqC a b (m+2) = a * b^m := rfl
      rw [e1, e2]; ring

theorem D_eq (a b : Nat) : (n : Nat) -> invertSeqD a b n = if n = 0 then 1
  else ∑ i ∈ Finset.range n, invertSeqC a b (n - i) * invertSeqD a b i := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have h1 : invertSeqD a b n = Nat.strongRecOn n (fun m ihs =>
      if m = 0 then 1
      else ∑ i ∈ Finset.range m,
        if h : i < m then invertSeqC a b (m - i) * ihs i h else 0) := rfl
    rw [h1]
    unfold Nat.strongRecOn
    rw [WellFounded.fix_eq]
    split
    · rfl
    · apply Finset.sum_congr rfl
      intro i hi
      rw [dif_pos (Finset.mem_range.mp hi)]
      rfl

theorem D_rec (a b : Nat) (m : Nat) :
    invertSeqD a b (m+2) + b * invertSeqD a b m
      = (1+b) * invertSeqD a b (m+1) + a * invertSeqD a b m := by
  have e2 := D_eq a b (m+2)
  have e1 := D_eq a b (m+1)
  rw [if_neg (by omega : ¬ (m+2 = 0)), Finset.sum_range_succ, Finset.sum_range_succ] at e2
  rw [if_neg (by omega : ¬ (m+1 = 0)), Finset.sum_range_succ] at e1
  norm_num at e2 e1
  have hC1 : invertSeqC a b 1 = 1 := rfl
  have hC2 : invertSeqC a b 2 = a := by simp [invertSeqC]
  have hA : ∑ i ∈ Finset.range m, invertSeqC a b (m+2-i) * invertSeqD a b i
         = b * ∑ i ∈ Finset.range m, invertSeqC a b (m+1-i) * invertSeqD a b i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have h2 : (m+1-i) + 1 = m+2-i := by omega
    have h3 : 2 <= m+1-i := by omega
    have h4 : invertSeqC a b ((m+1-i)+1) = b * invertSeqC a b (m+1-i) := C_succ a b (m+1-i) h3
    rw [show m+2-i = (m+1-i)+1 from by omega, h4]
    ring
  have hnorm : invertSeqC a b (m + 2 - (m + 1)) = invertSeqC a b 1 := by
    congr 1; omega
  rw [hnorm, hC1, hC2, hA] at e2
  rw [hC1] at e1
  rw [e2, e1]
  ring

theorem M2 (a b : Nat) :
    (genMatrix a b)^2 + b • (1 : Matrix (Fin 2) (Fin 2) Nat)
      = (1+b) • genMatrix a b + a • (1 : Matrix (Fin 2) (Fin 2) Nat) := by
  have hsmulM : ∀ (c : Nat) (M : Matrix (Fin 2) (Fin 2) Nat) (i j : Fin 2),
      (c • M) i j = c * M i j := by intro c M i j; simp [Matrix.smul_apply, smul_eq_mul]
  ext i j
  rw [pow_two]
  simp only [hsmulM, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply, genMatrix]
  fin_cases i <;> fin_cases j <;> simp [genMatrix] <;> ring

theorem Mpow_rec (a b m : Nat) :
    (genMatrix a b)^(m+2) + b • (genMatrix a b)^m
      = (1+b) • (genMatrix a b)^(m+1) + a • (genMatrix a b)^m := by
  have h := M2 a b
  have h2 : ((genMatrix a b)^2 + b • (1 : Matrix (Fin 2) (Fin 2) Nat)) * (genMatrix a b)^m
      = ((1+b) • genMatrix a b + a • (1 : Matrix (Fin 2) (Fin 2) Nat)) * (genMatrix a b)^m := by
    rw [h]
  rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      one_mul] at h2
  rw [← pow_add, ← pow_succ'] at h2
  have h3 : (2 : Nat) + m = m + 2 := by omega
  rw [h3] at h2
  exact h2

theorem entry_rec (a b m : Nat) :
    (genMatrix a b ^ (m+2)) 0 0 + b * (genMatrix a b ^ m) 0 0
      = (1+b) * (genMatrix a b ^ (m+1)) 0 0 + a * (genMatrix a b ^ m) 0 0 := by
  have h := Mpow_rec a b m
  have e0 := congrFun (congrFun h 0) 0
  simp only [Matrix.add_apply] at e0
  have hsmulM : ∀ (c : Nat) (M : Matrix (Fin 2) (Fin 2) Nat) (i j : Fin 2),
      (c • M) i j = c * M i j := by intro c M i j; simp [Matrix.smul_apply, smul_eq_mul]
  simp only [hsmulM] at e0
  exact e0

theorem swarm_proof (a b n : Nat) :
    invertSeqD a b n = (genMatrix a b ^ n) 0 0 := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [D_eq a b 0, if_pos rfl]
      simp [Matrix.one_apply]
  | one =>
      have D0 : invertSeqD a b 0 = 1 := by rw [D_eq a b 0, if_pos rfl]
      have C1 : invertSeqC a b 1 = 1 := rfl
      rw [D_eq a b 1, if_neg (by omega), Finset.range_one, Finset.sum_singleton, D0, C1]
      simp [genMatrix]
  | more k ih1 ih2 =>
      have hD := D_rec a b k
      have hE := entry_rec a b k
      rw [ih1, ih2] at hD
      omega
