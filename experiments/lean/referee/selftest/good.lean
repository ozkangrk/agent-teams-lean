import FormalConjectures.OEIS.«358684»
open OeisA358684 Nat

theorem swarm_proof : a 5 = 23 := by
  unfold a Nat.fermatNumber
  norm_num
  decide
