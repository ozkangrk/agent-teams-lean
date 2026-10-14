import FormalConjectures.Arxiv.«2507.17780».«2»
open SimpleGraph Arxiv.«2507.17780»
#check @Finset.pairwise_iff
#check @Finset.Pairwise.mono
#check @Finset.exists_subset_card_eq
#check @isIndepSet_iff
#check @isNIndepSet_iff
#check @Finset.card_insert_of_not_mem
example : ({0, 1, 2, 3, 4} : Finset (Fin 10)).card = 5 := by decide
