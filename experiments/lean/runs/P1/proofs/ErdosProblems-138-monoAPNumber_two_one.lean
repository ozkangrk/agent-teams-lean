
import FormalConjectures.ErdosProblems.«138»
/-! Warmup for Erdős 138: W 1 = 1. -/

open Erdos138


theorem mem_one : 1 ∈ monoAP_guarantee_set 2 1 := by
  intro coloring
  refine ⟨coloring ⟨1, by simp⟩, {⟨1, by simp⟩}, ?_, ?_⟩
  · show ((fun x : ↥(Finset.Icc 1 1) => (x : ℕ)) '' {⟨1, by simp⟩}).IsAPOfLength 1
    rw [Set.IsAPOfLength.one]
    refine ⟨1, ?_⟩
    simp [Set.image_singleton]
  · intro m hm
    have hm' : m = ⟨1, by simp⟩ := Set.mem_singleton_iff.mp hm
    rw [hm']

theorem not_mem_zero : 0 ∉ monoAP_guarantee_set 2 1 := by
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

theorem swarm_proof : Erdos138.W 1 = 1 := by
  apply le_antisymm
  · exact Nat.sInf_le mem_one
  · refine le_csInf ⟨1, mem_one⟩ ?_
    intro N hN
    exact Nat.pos_iff_ne_zero.2 (fun h0 => not_mem_zero (h0 ▸ hN))

