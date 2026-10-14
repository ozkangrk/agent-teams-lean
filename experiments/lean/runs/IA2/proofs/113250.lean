import FormalConjectures.OEIS.«113250»
set_option maxHeartbeats 2000000

namespace OeisA113250

private lemma rR (k : ℕ) : a (k + 4) = -4 * a (k + 3) + 64 * a (k + 1) + 256 * a k := rfl

private lemma key (n : ℕ) : a (n + 6) = 4096 * a n := by
  have e0 := rR n
  have e1 := rR (n + 1)
  have e2 := rR (n + 2)
  linarith

private lemma sq3 : ∀ t : ℕ, IsSquare (a (6 * t + 1)) ∧ IsSquare (a (6 * t + 3)) ∧ IsSquare (a (6 * t + 5)) := by
  intro t
  induction t with
  | zero =>
    exact ⟨⟨2, rfl⟩, ⟨8, rfl⟩, ⟨64, rfl⟩⟩
  | succ t ih =>
    obtain ⟨⟨s1, hs1⟩, ⟨s2, hs2⟩, ⟨s3, hs3⟩⟩ := ih
    have k1 : a (6 * (t + 1) + 1) = 4096 * a (6 * t + 1) := by
      rw [show 6 * (t + 1) + 1 = (6 * t + 1) + 6 from by omega]
      exact key (6 * t + 1)
    have k2 : a (6 * (t + 1) + 3) = 4096 * a (6 * t + 3) := by
      rw [show 6 * (t + 1) + 3 = (6 * t + 3) + 6 from by omega]
      exact key (6 * t + 3)
    have k3 : a (6 * (t + 1) + 5) = 4096 * a (6 * t + 5) := by
      rw [show 6 * (t + 1) + 5 = (6 * t + 5) + 6 from by omega]
      exact key (6 * t + 5)
    refine ⟨⟨64 * s1, ?_⟩, ⟨64 * s2, ?_⟩, ⟨64 * s3, ?_⟩⟩
    · rw [k1, hs1]; ring
    · rw [k2, hs2]; ring
    · rw [k3, hs3]; ring

end OeisA113250

open OeisA113250

theorem swarm_proof : type_of% @OeisA113250.conjecture := by
  intro n
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h | h | h
  · obtain ⟨t, rfl⟩ : ∃ t, n = 3 * t := ⟨n / 3, by omega⟩
    rw [show 2 * (3 * t) + 1 = 6 * t + 1 from by omega]
    exact (OeisA113250.sq3 t).1
  · obtain ⟨t, rfl⟩ : ∃ t, n = 3 * t + 1 := ⟨n / 3, by omega⟩
    rw [show 2 * (3 * t + 1) + 1 = 6 * t + 3 from by omega]
    exact (OeisA113250.sq3 t).2.1
  · obtain ⟨t, rfl⟩ : ∃ t, n = 3 * t + 2 := ⟨n / 3, by omega⟩
    rw [show 2 * (3 * t + 2) + 1 = 6 * t + 5 from by omega]
    exact (OeisA113250.sq3 t).2.2
