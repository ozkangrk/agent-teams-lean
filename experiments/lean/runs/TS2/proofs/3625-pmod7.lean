
import FormalConjectures.OEIS.«3625»
open Polynomial ZMod

theorem pmod7 (p : Nat) :
    IsSquare ((p : Nat) : ZMod 7) ↔ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by
  have hv : ((p : Nat) : ZMod 7) = ((p % 7 : Nat) : ZMod 7) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val (p : ZMod 7)]
    rw [ZMod.val_natCast]
  rw [hv]
  have hlt : p % 7 < 7 := by omega
  interval_cases p % 7 with h <;> rw [h] <;> decide
