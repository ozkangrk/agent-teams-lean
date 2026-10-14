
import FormalConjectures.OEIS.«108306»

open OeisA108306

-- probe available unfolding lemmas
#check @Nat.strongRecOn
#check @Nat.strongRecOn_eq_self
example (F : ∀ n, (∀ m, m < n → ℕ) → ℕ) (n : ℕ) :
    Nat.strongRecOn (n + 1) F = F (n + 1) (fun m _ => Nat.strongRecOn m F) := by
  rfl

theorem D_eq (a b : ℕ) : ∀ n, invertSeqD a b n = if n = 0 then 1
  else ∑ i ∈ Finset.range n, invertSeqC a b (n - i) * invertSeqD a b i := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [invertSeqD]
    split
    · rfl
    · congr 1
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i < n
      · rw [if_pos h]; rw [ih i h]
      · rw [if_neg h]
