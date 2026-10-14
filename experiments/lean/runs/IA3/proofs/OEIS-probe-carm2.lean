import FormalConjectures.OEIS.«237271»
import FormalConjectures.Wikipedia.AgohGiuga

open Nat Finset List

#check @AgohGiuga.korselts_criterion
#check @AgohGiuga.squarefree_of_isCarmichael
#check @AgohGiuga.IsCarmichael
-- find sorted lemma
example (s : Finset Nat) : (s.sort (· ≤ ·)).Sorted (· ≤ ·) := Finset.sorted_sort (· ≤ ·) s
