import FormalConjectures.OEIS.«306477»

open OeisA306477

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1000000 in
theorem swarm_proof : ¬ ∀ n : ℕ, 0 < n → A n := by
  intro h
  have hN : A 23253 := h 23253 (by norm_num)
  obtain ⟨w, x, y, z, heq⟩ := hN
  have hw : w < 215 := by
    by_contra hc
    have hge : 215 ≤ w := by omega
    have m1 : (217).choose 2 ≤ (w + 2).choose 2 := Nat.choose_mono 2 (by omega)
    have m2 : (217).choose 2 = 23436 := by rfl
    have m3 : (w + 2).choose 2 ≤ 23253 := by omega
    omega
  have hx : x < 26 := by
    by_contra hc
    have hge : 26 ≤ x := by omega
    have m1 : (29).choose 4 ≤ (x + 3).choose 4 := Nat.choose_mono 4 (by omega)
    have m2 : (29).choose 4 = 23751 := by rfl
    have m3 : (x + 3).choose 4 ≤ 23253 := by omega
    omega
  have hy : y < 14 := by
    by_contra hc
    have hge : 14 ≤ y := by omega
    have m1 : (19).choose 6 ≤ (y + 5).choose 6 := Nat.choose_mono 6 (by omega)
    have m2 : (19).choose 6 = 27132 := by rfl
    have m3 : (y + 5).choose 6 ≤ 23253 := by omega
    omega
  have hz : z < 10 := by
    by_contra hc
    have hge : 10 ≤ z := by omega
    have m1 : (17).choose 8 ≤ (z + 7).choose 8 := Nat.choose_mono 8 (by omega)
    have m2 : (17).choose 8 = 24310 := by rfl
    have m3 : (z + 7).choose 8 ≤ 23253 := by omega
    omega
  have hw2 : w + 2 < 217 := by omega
  have key : ∀ x' < 26, ∀ y' < 14, ∀ z' < 10,
      ¬ (23253 - (x' + 3).choose 4 - (y' + 5).choose 6 - (z' + 7).choose 8)
        ∈ (Finset.range 217).image (fun k : ℕ => k.choose 2) := by
    decide
  have hrest : 23253 - (x + 3).choose 4 - (y + 5).choose 6 - (z + 7).choose 8 = (w + 2).choose 2 := by
    have h1 : (x + 3).choose 4 ≤ 23253 := by omega
    have h2 : (y + 5).choose 6 ≤ 23253 := by omega
    have h3 : (z + 7).choose 8 ≤ 23253 := by omega
    omega
  have hmem : (23253 - (x + 3).choose 4 - (y + 5).choose 6 - (z + 7).choose 8) ∈ tri := by
    rw [hrest]
    exact Finset.mem_image_of_mem (f := fun k : ℕ => k.choose 2) (Finset.mem_range.mpr hw2)
  exact key x hx y hy z hz hmem
