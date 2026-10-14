import FormalConjectures.Arxiv.«2507.17780».«2»
/-! Scratch scaffold for tx_graffiti_conjecture_2 machinery. -/

open SimpleGraph Arxiv.«2507.17780»

/-- Edge list of the graph (undirected, canonical orientation). -/
def E : List (ℕ × ℕ) := [
    (0, 1),
    (1, 2),
    (2, 3),
    (3, 4),
    (0, 4),
    (5, 7),
    (6, 8),
    (7, 9),
    (5, 8),
    (6, 9),
    (0, 5),
    (1, 6),
    (2, 7),
    (3, 8),
    (4, 9),
    ]

/-- The graph on `Fin 10` whose adjacency is given by `E`. -/
def G : SimpleGraph (Fin 10) where
  Adj := fun u v => (min u.val v.val, max u.val v.val) ∈ E
  symm := fun u v h => by
    have hmin : min v.val u.val = min u.val v.val := Nat.min_comm _ _
    have hmax : max v.val u.val = max u.val v.val := Nat.max_comm _ _
    simp only [G.Adj] at h ⊢
    rw [hmin, hmax] at h
    exact h
  loopless := fun v h => by
    simp only [G.Adj, Nat.min_self, Nat.max_self] at h
    simp [E] at h

instance : DecidableRel G.Adj := by
  intro u v
  unfold G.Adj
  infer_instance
