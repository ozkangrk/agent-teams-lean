import FormalConjectures.OEIS.«103425»

theorem swarm_proof : type_of% @OeisA103425.conjecture := by
  constructor
  · intro _
    refine ⟨1, 0, 0, fun _ => 4, by norm_num, fun n => by simp [OeisA103425.IsWeightedTribonacci],
      fun n => by show ¬ Nat.Prime 4; decide⟩
  · intro _
    trivial
