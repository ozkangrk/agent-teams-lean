
import FormalConjectures.OEIS.«108306»

open OeisA108306
open Matrix

-- experiment: unfold strongRecOn
example (a b : ℕ) (n : ℕ) : invertSeqD a b n = Nat.strongRecOn n (fun m ih =>
      if m = 0 then 1
      else ∑ i ∈ Finset.range m,
        if h : i < m then invertSeqC a b (m - i) * ih i h else 0) := by
  rfl

#check @Nat.strongRecOn
example (a b : ℕ) : ∀ n, invertSeqD a b n = if n = 0 then 1
  else ∑ i ∈ Finset.range n, invertSeqC a b (n - i) * invertSeqD a b i := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    sorry
