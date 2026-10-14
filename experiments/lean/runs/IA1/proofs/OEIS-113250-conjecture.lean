import FormalConjectures.OEIS.«113250»

theorem swarm_proof : ∀ n : ℕ, IsSquare (OeisA113250.a (2 * n + 1)) := by
  have key : ∀ k : ℕ, OeisA113250.a (6 * k) = -(2:ℤ) ^ (12 * k)
      ∧ OeisA113250.a (6 * k + 1) = (2:ℤ) ^ (12 * k + 2)
      ∧ OeisA113250.a (6 * k + 2) = (2:ℤ) ^ (12 * k + 5)
      ∧ OeisA113250.a (6 * k + 3) = (2:ℤ) ^ (12 * k + 6)
      ∧ OeisA113250.a (6 * k + 4) = -(2:ℤ) ^ (12 * k + 8)
      ∧ OeisA113250.a (6 * k + 5) = (2:ℤ) ^ (12 * k + 12) := by
    intro k
    induction k with
    | zero => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | succ k ih =>
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := ih
      have g0 : OeisA113250.a (6 * k + 6) = -(2:ℤ) ^ (12 * k + 12) := by
        rw [show 6*k+6 = (6*k+2)+4 by ring, OeisA113250.a,
          show (6*k+2)+3 = 6*k+5 by ring, show (6*k+2)+1 = 6*k+3 by ring, h5, h3, h2]
        simp only [pow_add]
        norm_num
        ring
      have g1 : OeisA113250.a (6 * k + 7) = (2:ℤ) ^ (12 * k + 14) := by
        rw [show 6*k+7 = (6*k+3)+4 by ring, OeisA113250.a,
          show (6*k+3)+3 = 6*k+6 by ring, show (6*k+3)+1 = 6*k+4 by ring, g0, h4, h3]
        simp only [pow_add]
        norm_num
        ring
      have g2 : OeisA113250.a (6 * k + 8) = (2:ℤ) ^ (12 * k + 17) := by
        rw [show 6*k+8 = (6*k+4)+4 by ring, OeisA113250.a,
          show (6*k+4)+3 = 6*k+7 by ring, show (6*k+4)+1 = 6*k+5 by ring, g1, h5, h4]
        simp only [pow_add]
        norm_num
        ring
      have g3 : OeisA113250.a (6 * k + 9) = (2:ℤ) ^ (12 * k + 18) := by
        rw [show 6*k+9 = (6*k+5)+4 by ring, OeisA113250.a,
          show (6*k+5)+3 = 6*k+8 by ring, show (6*k+5)+1 = 6*k+6 by ring, g2, g0, h5]
        simp only [pow_add]
        norm_num
        ring
      have g4 : OeisA113250.a (6 * k + 10) = -(2:ℤ) ^ (12 * k + 20) := by
        rw [show 6*k+10 = (6*k+6)+4 by ring, OeisA113250.a,
          show (6*k+6)+3 = 6*k+9 by ring, show (6*k+6)+1 = 6*k+7 by ring, g3, g1, g0]
        simp only [pow_add]
        norm_num
        ring
      have g5 : OeisA113250.a (6 * k + 11) = (2:ℤ) ^ (12 * k + 24) := by
        rw [show 6*k+11 = (6*k+7)+4 by ring, OeisA113250.a,
          show (6*k+7)+3 = 6*k+10 by ring, show (6*k+7)+1 = 6*k+8 by ring, g4, g2, g1]
        simp only [pow_add]
        norm_num
        ring
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show 6*(k+1) = 6*k+6 by ring]; exact g0
      · rw [show 6*(k+1)+1 = 6*k+7 by ring,
          show 12*(k+1)+2 = 12*k+14 by omega]; exact g1
      · rw [show 6*(k+1)+2 = 6*k+8 by ring,
          show 12*(k+1)+5 = 12*k+17 by omega]; exact g2
      · rw [show 6*(k+1)+3 = 6*k+9 by ring,
          show 12*(k+1)+6 = 12*k+18 by omega]; exact g3
      · rw [show 6*(k+1)+4 = 6*k+10 by ring,
          show 12*(k+1)+8 = 12*k+20 by omega]; exact g4
      · rw [show 6*(k+1)+5 = 6*k+11 by ring,
          show 12*(k+1)+12 = 12*k+24 by omega]; exact g5
  intro n
  rcases h : n % 3 with _ | _ | _
  · rw [show 2*n+1 = 6*(n/3)+1 by omega, (key (n/3)).2.1]
    exact ⟨(2:ℤ)^(6*(n/3)+1), by rw [← pow_add]; congr 1; omega⟩
  · rw [show 2*n+1 = 6*(n/3)+3 by omega, (key (n/3)).2.2.2.1]
    exact ⟨(2:ℤ)^(6*(n/3)+3), by rw [← pow_add]; congr 1; omega⟩
  · rw [show 2*n+1 = 6*(n/3)+5 by omega, (key (n/3)).2.2.2.2.2]
    exact ⟨(2:ℤ)^(6*(n/3)+6), by rw [← pow_add]; congr 1; omega⟩
