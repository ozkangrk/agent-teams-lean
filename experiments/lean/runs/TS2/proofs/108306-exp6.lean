
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
    · have hconv : ∀ i ∈ Finset.range n,
        (if h : i < n then invertSeqC a b (n - i) * Nat.strongRecOn (fun m ihs =>
          if m = 0 then 1 else ∑ i ∈ Finset.range m,
            if h : i < m then invertSeqC a b (m - i) * ihs i h else 0) i else 0)
          = invertSeqC a b (n - i) * invertSeqD a b i := by
        intro i hi
        rw [if_pos (Finset.mem_range.mp hi)]
      rw [Finset.sum_congr rfl hconv]
