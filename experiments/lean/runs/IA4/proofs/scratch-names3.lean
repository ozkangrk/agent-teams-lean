import FormalConjectures.Arxiv.«2507.17780».«2»
open SimpleGraph Arxiv.«2507.17780»
#check @Set.Pairwise.mono
#check @Finset.mem_coe
#check @Finset.mem_coe.mp
example : ({0, 1, 2, 3, 4} : Finset (Fin 10)).card = 5 := by simp
example : ({0, 1, 2, 3, 4} : Finset (Fin 10)).card = 5 := by decide
