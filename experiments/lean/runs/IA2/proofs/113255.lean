
import FormalConjectures.OEIS.«113255»
set_option maxHeartbeats 2000000

namespace OeisA113255

private lemma rRe (k : ℕ) : a (k + 4) = -4 * a (k + 3) + 324 * a (k + 1) + 6561 * a k := rfl

private lemma rR (k : ℕ) : a (k + 4) + 4 * a (k + 3) - 324 * a (k + 1) - 6561 * a k = 0 := by
  have h := rRe k
  linarith

private lemma Trec (m : ℕ) :
    a (m + 7) + 65 * a (m + 5) - 5265 * a (m + 3) - 531441 * a (m + 1) = 0 := by
  have h1 := rR (m + 1)
  have h2 := rR (m + 2)
  have h3 := rR (m + 3)
  linear_combination h3 - 4 * h2 + 81 * h1

private def b : ℕ → ℤ
  | 0 => 2
  | 1 => 73
  | n + 2 => -4 * b (n + 1) - 81 * b n

private lemma main : ∀ n : ℕ, a (2 * n + 1) = (b n) ^ 2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match h : n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | m + 3 =>
      have t := Trec (2 * m)
      have p1 : a (2 * m + 1) = (b m) ^ 2 := ih m (by omega)
      have p2 : a (2 * (m + 1) + 1) = (b (m + 1)) ^ 2 := ih (m + 1) (by omega)
      have p3 : a (2 * (m + 2) + 1) = (b (m + 2)) ^ 2 := ih (m + 2) (by omega)
      have p2' : a (2 * m + 3) = (b (m + 1)) ^ 2 := by
        rw [show 2 * m + 3 = 2 * (m + 1) + 1 from by omega]; exact p2
      have p3' : a (2 * m + 5) = (b (m + 2)) ^ 2 := by
        rw [show 2 * m + 5 = 2 * (m + 2) + 1 from by omega]; exact p3
      have br1 : b (m + 3) = -4 * b (m + 2) - 81 * b (m + 1) := rfl
      have br2 : b (m + 2) = -4 * b (m + 1) - 81 * b m := rfl
      have key : (b (m + 3)) ^ 2 + 65 * (b (m + 2)) ^ 2
          - 5265 * (b (m + 1)) ^ 2 - 531441 * (b m) ^ 2 = 0 := by
        rw [br1, br2]; ring
      rw [show 2 * (m + 3) + 1 = 2 * m + 7 from by omega]
      linarith [t, p1, p2', p3', key]

end OeisA113255

open OeisA113255

theorem swarm_proof : type_of% @OeisA113255.conjecture := by
  intro n
  exact ⟨b n, by rw [main n]; ring⟩
