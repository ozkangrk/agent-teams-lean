
import FormalConjectures.ErdosProblems.«138»
/-! Warmup for Erdős 138: W 2 = 3. -/

open Erdos138

theorem mem_three : 3 ∈ monoAP_guarantee_set 2 2 := by
  intro coloring
  by_cases h12 : coloring ⟨1, by norm_num⟩ = coloring ⟨2, by norm_num⟩
  · refine ⟨coloring ⟨1, by norm_num⟩, {⟨1, by norm_num⟩, ⟨2, by norm_num⟩}, ?_, ?_⟩
    · show ((fun x : ↥(Finset.Icc 1 3) => (x : ℕ)) ''
        {⟨1, by norm_num⟩, ⟨2, by norm_num⟩}).IsAPOfLength 2
      have himg : (fun x : ↥(Finset.Icc 1 3) => (x : ℕ)) ''
          {⟨1, by norm_num⟩, ⟨2, by norm_num⟩} = {1, 2} := by
        rw [Set.image_pair]
      rw [himg]
      exact Nat.isAPOfLength_pair (by norm_num)
    · intro m hm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with rfl | rfl
      · rfl
      · exact h12.symm
  · by_cases h23 : coloring ⟨2, by norm_num⟩ = coloring ⟨3, by norm_num⟩
    · refine ⟨coloring ⟨2, by norm_num⟩, {⟨2, by norm_num⟩, ⟨3, by norm_num⟩}, ?_, ?_⟩
      · show ((fun x : ↥(Finset.Icc 1 3) => (x : ℕ)) ''
          {⟨2, by norm_num⟩, ⟨3, by norm_num⟩}).IsAPOfLength 2
        have himg : (fun x : ↥(Finset.Icc 1 3) => (x : ℕ)) ''
            {⟨2, by norm_num⟩, ⟨3, by norm_num⟩} = {2, 3} := by
          rw [Set.image_pair]
        rw [himg]
        exact Nat.isAPOfLength_pair (by norm_num)
      · intro m hm
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        rcases hm with rfl | rfl
        · rfl
        · exact h23.symm
    · have h13 : coloring ⟨1, by norm_num⟩ = coloring ⟨3, by norm_num⟩ := by
        have b1 : (coloring ⟨1, by norm_num⟩ : ℕ) < 2 := (coloring ⟨1, by norm_num⟩).is_lt
        have b2 : (coloring ⟨2, by norm_num⟩ : ℕ) < 2 := (coloring ⟨2, by norm_num⟩).is_lt
        have b3 : (coloring ⟨3, by norm_num⟩ : ℕ) < 2 := (coloring ⟨3, by norm_num⟩).is_lt
        have e12 : (coloring ⟨1, by norm_num⟩ : ℕ) ≠ (coloring ⟨2, by norm_num⟩ : ℕ) :=
          fun he => h12 (Fin.val_injective he)
        have e23 : (coloring ⟨2, by norm_num⟩ : ℕ) ≠ (coloring ⟨3, by norm_num⟩ : ℕ) :=
          fun he => h23 (Fin.val_injective he)
        exact Fin.val_injective (by omega)
      refine ⟨coloring ⟨1, by norm_num⟩, {⟨1, by norm_num⟩, ⟨3, by norm_num⟩}, ?_, ?_⟩
      · show ((fun x : ↥(Finset.Icc 1 3) => (x : ℕ)) ''
          {⟨1, by norm_num⟩, ⟨3, by norm_num⟩}).IsAPOfLength 2
        have himg : (fun x : ↥(Finset.Icc 1 3) => (x : ℕ)) ''
            {⟨1, by norm_num⟩, ⟨3, by norm_num⟩} = {1, 3} := by
          rw [Set.image_pair]
        rw [himg]
        exact Nat.isAPOfLength_pair (by norm_num)
      · intro m hm
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        rcases hm with rfl | rfl
        · rfl
        · exact h13.symm

theorem not_mem_zero_two : 0 ∉ monoAP_guarantee_set 2 2 := by
  intro h
  obtain ⟨c, ap, hap, -⟩ := h (fun _ => 0)
  have hiso : IsEmpty ↥(Finset.Icc 1 0) := by
    refine isEmpty_iff.mpr ?_
    intro x
    have hx := x.2
    simp only [Finset.mem_Icc] at hx
    omega
  have hap' : ap = ∅ := Set.eq_empty_of_isEmpty ap
  rw [hap', Set.image_empty] at hap
  exact Set.not_isAPOfLength_empty (by decide) hap

theorem not_mem_one : 1 ∉ monoAP_guarantee_set 2 2 := by
  intro h
  obtain ⟨c, ap, hap, -⟩ := h (fun _ => 0)
  have hsub : (fun x : ↥(Finset.Icc 1 1) => (x : ℕ)) '' ap ⊆ {1} := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx1 := x.2
    simp only [Finset.mem_Icc] at hx1
    simp
    omega
  have h2 : ((fun x : ↥(Finset.Icc 1 1) => (x : ℕ)) '' ap).encard = 2 := hap.card
  have hle := Set.encard_mono hsub
  rw [h2, Set.encard_singleton] at hle
  exact absurd hle (by decide)

theorem not_mem_two : 2 ∉ monoAP_guarantee_set 2 2 := by
  intro h
  obtain ⟨c, ap, hap, hmono⟩ := h (fun x => if (x : ℕ) = 2 then (1 : Fin 2) else 0)
  have hsub : (fun x : ↥(Finset.Icc 1 2) => (x : ℕ)) '' ap ⊆ {1, 2} := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx1 := x.2
    simp only [Finset.mem_Icc] at hx1
    simp
    omega
  have h2 : ((fun x : ↥(Finset.Icc 1 2) => (x : ℕ)) '' ap).encard = 2 := hap.card
  have hfin : ({1, 2} : Set ℕ).Finite := by simp
  have hcard2 : ({1, 2} : Set ℕ).encard = 2 := by
    rw [Set.encard_insert_of_notMem (by simp), Set.encard_singleton]
    rfl
  have himg : (fun x : ↥(Finset.Icc 1 2) => (x : ℕ)) '' ap = {1, 2} :=
    (hfin.subset hsub).eq_of_subset_of_encard_le hsub (by rw [hcard2, h2])
  have h1 : (1 : ℕ) ∈ (fun x : ↥(Finset.Icc 1 2) => (x : ℕ)) '' ap := by
    rw [himg]; simp
  have h2' : (2 : ℕ) ∈ (fun x : ↥(Finset.Icc 1 2) => (x : ℕ)) '' ap := by
    rw [himg]; simp
  obtain ⟨x, hx, hx1⟩ := h1
  obtain ⟨y, hy, hy1⟩ := h2'
  have hcx := hmono x hx
  have hcy := hmono y hy
  have ex : (fun x : ↥(Finset.Icc 1 2) => if (x : ℕ) = 2 then (1 : Fin 2) else 0) x = 0 := by
    simp [hx1]
  have ey : (fun x : ↥(Finset.Icc 1 2) => if (x : ℕ) = 2 then (1 : Fin 2) else 0) y = 1 := by
    simp [hy1]
  rw [ex] at hcx
  rw [ey] at hcy
  exact absurd (hcy.trans hcx.symm) (by decide)

theorem swarm_proof : Erdos138.W 2 = 3 := by
  apply le_antisymm
  · exact Nat.sInf_le mem_three
  · refine le_csInf ⟨3, mem_three⟩ ?_
    intro N hN
    by_cases h3 : 3 ≤ N
    · exact h3
    · exfalso
      have hN2 : N ≤ 2 := by omega
      interval_cases N
      · exact not_mem_zero_two hN
      · exact not_mem_one hN
      · exact not_mem_two hN
