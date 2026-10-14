
import FormalConjectures.OEIS.«108306»
open OeisA108306
#check @Nat.strongRecOn.eq_1

example (F : (n : Nat) → ((m : Nat) → m < n → Nat) → Nat) (n : Nat) :
    Nat.strongRecOn (n + 1) F = F (n + 1) (fun m _ => Nat.strongRecOn m F) := by
  rw [Nat.strongRecOn.eq_1]

theorem D_eq (a b : Nat) : (n : Nat) → invertSeqD a b n = if n = 0 then 1
  else ∑ i ∈ Finset.range n, invertSeqC a b (n - i) * invertSeqD a b i := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have h1 : invertSeqD a b n = Nat.strongRecOn n (fun m ihs =>
      if m = 0 then 1
      else ∑ i ∈ Finset.range m, if h : i < m then invertSeqC a b (m - i) * ihs i h else 0) := rfl
    rw [h1, Nat.strongRecOn.eq_1]
    split
    · rfl
    · congr 1
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i < n
      · rw [if_pos h, ih i h]
      · rw [if_neg h]
