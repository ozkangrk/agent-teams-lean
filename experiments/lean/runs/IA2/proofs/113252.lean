
import FormalConjectures.OEIS.«113252»
set_option maxHeartbeats 2000000

namespace OeisA113252

private lemma rRe (k : ℕ) : a (k + 4) = -4 * a (k + 3) + 144 * a (k + 1) + 1296 * a k := rfl

private lemma rR (k : ℕ) : a (k + 4) + 4 * a (k + 3) - 144 * a (k + 1) - 1296 * a k = 0 := by
  have h := rRe k
  linarith

private lemma Trec (m : ℕ) :
    a (m + 7) + 20 * a (m + 5) - 720 * a (m + 3) - 46656 * a (m + 1) = 0 := by
  have h1 := rR (m + 1)
  have h2 := rR (m + 2)
  have h3 := rR (m + 3)
  linear_combination h3 - 4 * h2 + 36 * h1

private def x : ℕ → ℤ
  | 0 => 1
  | 1 => 14
  | n + 2 => -4 * x (n + 1) - 36 * x n

private lemma main : ∀ n : ℕ, a (2 * n + 1) = (2 * x n) ^ 2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match h : n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | m + 3 =>
      have t := Trec (2 * m)
      have p1 : a (2 * m + 1) = (2 * x m) ^ 2 := ih m (by omega)
      have p2 : a (2 * (m + 1) + 1) = (2 * x (m + 1)) ^ 2 := ih (m + 1) (by omega)
      have p3 : a (2 * (m + 2) + 1) = (2 * x (m + 2)) ^ 2 := ih (m + 2) (by omega)
      have p2' : a (2 * m + 3) = (2 * x (m + 1)) ^ 2 := by
        rw [show 2 * m + 3 = 2 * (m + 1) + 1 from by omega]; exact p2
      have p3' : a (2 * m + 5) = (2 * x (m + 2)) ^ 2 := by
        rw [show 2 * m + 5 = 2 * (m + 2) + 1 from by omega]; exact p3
      have xr1 : x (m + 3) = -4 * x (m + 2) - 36 * x (m + 1) := rfl
      have xr2 : x (m + 2) = -4 * x (m + 1) - 36 * x m := rfl
      have key : (2 * x (m + 3)) ^ 2 + 20 * (2 * x (m + 2)) ^ 2
          - 720 * (2 * x (m + 1)) ^ 2 - 46656 * (2 * x m) ^ 2 = 0 := by
        rw [xr1, xr2]; ring
      rw [show 2 * (m + 3) + 1 = 2 * m + 7 from by omega]
      linarith [t, p1, p2', p3', key]

end OeisA113252

open OeisA113252

theorem swarm_proof : type_of% @OeisA113252.conjecture := by
  intro n
  exact ⟨2 * x n, by rw [main n]; ring⟩
