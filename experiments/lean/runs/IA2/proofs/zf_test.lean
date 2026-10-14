
import FormalConjectures.Arxiv.«2507.17780».«2»

open Finset SimpleGraph

namespace ZFTest

abbrev n : ℕ := 10
def E : Finset (Sym2 (Fin n)) :=
  {{0, 1}, {0, 4}, {0, 5}, {1, 2}, {1, 6}, {2, 3}, {2, 7}, {3, 4}, {3, 8},
   {4, 9}, {5, 7}, {5, 8}, {6, 8}, {6, 9}, {7, 9}}

def Gc : SimpleGraph (Fin n) := fromEdgeSet E

instance : DecidableRel Gc.Adj := fun a b => Finset.decidableMem _ _

-- computable forcing step
def zfStep (S : Finset (Fin n)) : Finset (Fin n) :=
  S ∪ Finset.univ.filter fun w => w ∉ S ∧ ∃ v ∈ S, Gc.Adj v w ∧
    ∀ u ∈ Finset.univ.filter (fun u => Gc.Adj v u), u = w ∨ u ∈ S

def zfCl (S : Finset (Fin n)) : Finset (Fin n) := (zfStep)^[n] S

-- zeroForcingStep Gc S = zfStep S
theorem step_eq (S : Finset (Fin n)) :
    Arxiv.«2507.17780».«2».zeroForcingStep Gc S = zfStep S := by
  ext w
  simp only [Arxiv.«2507.17780».«2».zeroForcingStep, zfStep, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ]
  constructor
  · rintro (h | ⟨h1, v, hvS, hadj, hall⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h1, v, hvS, hadj, ?_⟩
      intro u hu hns
      have := hall u (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩)
      rcases this with heq | hm
      · exact heq
      · exact absurd hm hns
  · rintro (h | ⟨h1, v, hvS, hadj, hall⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h1, v, hvS, hadj, ?_⟩
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rcases hall u hu with heq | hm
      · exact Or.inl heq
      · exact Or.inr hm

theorem cl_eq (S : Finset (Fin n)) :
    Arxiv.«2507.17780».«2».zeroForcingClosure Gc S = zfCl S := by
  unfold zfCl Arxiv.«2507.17780».«2».zeroForcingClosure
  rw [Fintype.card_fin]
  induction n with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ, Function.iterate_succ, ← ih, ← step_eq]

-- sanity: check a forcing set of size 5 works (Petersen Z = 5)
example : zfCl {0, 1, 2, 3, 6} = Finset.univ := by decide

-- min side: no forcing set of size ≤ 4
example : ∀ S : Finset (Fin n), ¬ (S.card ≤ 4 ∧ zfCl S = Finset.univ) := by decide

end ZFTest
