import FormalConjectures.Arxiv.«2507.17780».«2»

open SimpleGraph Arxiv.«2507.17780»

-- test 1: does answer(False) reduce to False?
example : answer(False) ↔ False := by
  constructor
  · intro h; exact h
  · intro h; exact h.elim

-- test 2: small graph on Fin 3, decidable connected?
def Gt : SimpleGraph (Fin 3) where
  Adj u v := u.val + v.val = 1
  symm u v h := by simp [Nat.add_comm] at h ⊢; omega
  loop v := by simp [Adj]

instance : DecidableRel Gt.Adj := by unfold Gt; infer_instance

example : Gt.Connected := by decide!

end
