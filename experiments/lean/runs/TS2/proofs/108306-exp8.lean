
import FormalConjectures.OEIS.«108306»

open OeisA108306
open Matrix

theorem C_succ (a b : Nat) : {j : Nat} -> 2 <= j -> invertSeqC a b (j+1) = b * invertSeqC a b j
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
      rw [if_pos (Finset.mem_range.mp hi)]

theorem D_rec (a b : Nat) (m : Nat) :
    invertSeqD a b (m+2) + b * invertSeqD a b m
      = (1+b) * invertSeqD a b (m+1) + a * invertSeqD a b m := by
  have e2 := D_eq a b (m+2)
  have e1 := D_eq a b (m+1)
  rw [if_neg (by omega : ¬ (m+2 = 0))] at e2
  rw [if_neg (by omega : ¬ (m+1 = 0))] at e1
  rw [Finset.range_succ, Finset.sum_insert (by simp), Finset.range_succ,
      Finset.sum_insert (by simp)] at e2
  rw [Finset.range_succ, Finset.sum_insert (by simp)] at e1
  have hC1 : invertSeqC a b 1 = 1 := rfl
  have hC2 : invertSeqC a b 2 = a := rfl
  have hA : ∑ i ∈ Finset.range m, invertSeqC a b (m+2-i) * invertSeqD a b i
         = b * ∑ i ∈ Finset.range m, invertSeqC a b (m+1-i) * invertSeqD a b i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have h2 : (m+1-i) + 1 = m+2-i := by omega
    have h3 : 2 <= m+1-i := by omega
    have h4 : invertSeqC a b ((m+1-i)+1) = b * invertSeqC a b (m+1-i) := C_succ a b _ h3
    rw [show m+2-i = (m+1-i)+1 from by omega, h4]
    ring
  rw [hC1, hC2, hA] at e2
  rw [hC1] at e1
  rw [e2, e1]
  ring
