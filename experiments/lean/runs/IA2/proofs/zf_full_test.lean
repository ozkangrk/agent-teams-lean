
import FormalConjectures.Arxiv.«2507.17780».«2»

open Finset SimpleGraph
open Arxiv.«2507.17780»

namespace ZFFull

abbrev n : ℕ := 10
def E : Finset (Sym2 (Fin n)) :=
  {{0, 1}, {0, 4}, {0, 5}, {1, 2}, {1, 6}, {2, 3}, {2, 7}, {3, 4}, {3, 8},
   {4, 9}, {5, 7}, {5, 8}, {6, 8}, {6, 9}, {7, 9}}

def Gc : SimpleGraph (Fin n) := fromEdgeSet E

instance : DecidableRel Gc.Adj := fun a b =>
  decidable_of_decidable_of_iff (Finset.decidableMem (⟦(a, b)⟧ : Sym2 (Fin n)) E) (by rfl)

def zfStep (S : Finset (Fin n)) : Finset (Fin n) :=
  S ∪ Finset.univ.filter fun w => w ∉ S ∧ ∃ v ∈ S, Gc.Adj v w ∧
    ∀ u ∈ Finset.univ.filter (fun u => Gc.Adj v u), u = w ∨ u ∈ S

def zfCl (S : Finset (Fin n)) : Finset (Fin n) := (zfStep)^[n] S

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

abbrev ZN : ℕ := 5
abbrev IN : ℕ := 4
def Sw : Finset (Fin n) := {0, 1, 2, 3, 6}

theorem hwit : IsZeroForcingSet Gc Sw := by
  rw [IsZeroForcingSet, cl_eq]
  decide

theorem hmin : ∀ S : Finset (Fin n), ¬ (S.card ≤ ZN - 1 ∧ zfCl S = Finset.univ) := by decide

theorem hZ : zeroForcingNumber Gc = ZN := by
  unfold zeroForcingNumber
  apply le_antisymm
  · exact Nat.sInf_le ⟨ZN, ⟨Sw, rfl, hwit⟩⟩
  · by_contra hc
    have hlt : zeroForcingNumber Gc < ZN := by omega
    have hne : {k | ∃ S, S.card = k ∧ IsZeroForcingSet Gc S}.Nonempty :=
      ⟨ZN, ⟨Sw, rfl, hwit⟩⟩
    obtain ⟨k, hk⟩ := Nat.sInf_mem hne
    obtain ⟨S, hcard, hforce⟩ := hk
    exact hmin S ⟨by rw [hcard]; omega, hforce⟩

def Iw : Finset (Fin n) := {0, 2, 8, 9}

theorem hInd : Gc.IsIndepSet Iw := by
  have hb : ∀ v ∈ Iw, ∀ w ∈ Iw, v = w ∨ ¬ Gc.Adj v w := by decide
  rw [Gc.isIndepSet_iff]
  intro v hv w hw hne
  rcases hb v (Finset.mem_coe.mp hv) w (Finset.mem_coe.mp hw) with rfl|h
  · exact absurd rfl hne
  · exact h

theorem hα : Gc.indepNum = IN := by
  have hno : ∀ f : Fin n → Bool,
      ¬ (Finset.card (Finset.univ.filter (fun v => f v = true)) = IN + 1 ∧
         (∀ v : Fin n, ∀ w : Fin n, f v = false ∨ f w = false ∨ v = w ∨ ¬ Gc.Adj v w)) := by
    decide
  apply le_antisymm
  · by_contra hc
    have h2 : IN < Gc.indepNum := by omega
    obtain ⟨s, hs⟩ := Gc.exists_isNIndepSet_indepNum
    have hcard : #s = Gc.indepNum := hs.2
    obtain ⟨t, ht1, ht2⟩ := Finset.exists_subset_card_eq (s := s) (n := IN + 1) (by omega)
    have hsub : ∀ x ∈ t, x ∈ s := ht1
    set f : Fin n → Bool := fun v => (Finset.decidableMem v t).toBool with hf
    have hfm : ∀ x : Fin n, f x = true ↔ x ∈ t := by
      intro x
      cases h : Finset.decidableMem x t with
      | isTrue hT => simp [hf]
      | isFalse hF => simp [hf, hF]
    have hfilter : Finset.univ.filter (fun v => f v = true) = t := by
      ext x
      rw [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hfm x
    have inner : ∀ v : Fin n, ∀ w : Fin n, f v = false ∨ f w = false ∨ v = w ∨ ¬ Gc.Adj v w := by
      intro v w
      rcases eq_or_ne (f v) true with hv | hv
      · rcases eq_or_ne (f w) true with hw | hw
        · rcases eq_or_ne v w with rfl | hne
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr
              ((Gc.isIndepSet_iff).mp hs.isIndepSet (Finset.mem_coe.mpr (ht1 ((hfm v).mp hv)))
                (Finset.mem_coe.mpr (ht1 ((hfm w).mp hw))) hne)))
        · exact Or.inr (Or.inl (by simp [hw]))
      · exact Or.inl (by simp [hv])
    exact hno f ⟨by rw [hfilter]; exact ht2, inner⟩
  · exact hInd.card_le_indepNum

end ZFFull
