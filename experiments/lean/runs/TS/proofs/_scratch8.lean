import FormalConjectures.OEIS.«108306»
open OeisA108306

example (a b : ℕ) : invertSeqD a b 0 = 1 := by
  unfold invertSeqD Nat.strongRecOn
  rw [WellFounded.fix_eq, if_pos rfl]

example (a b : ℕ) (m : ℕ) (hm : 0 < m) :
    invertSeqD a b m = ∑ i ∈ Finset.range m, invertSeqC a b (m - i) * invertSeqD a b i := by
  unfold invertSeqD Nat.strongRecOn
  rw [WellFounded.fix_eq, if_neg (show ¬ m = 0 by omega)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [dif_pos (Finset.mem_range.mp hi)]
