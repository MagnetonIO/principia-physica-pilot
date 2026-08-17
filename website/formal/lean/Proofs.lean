import Std

/-!
# Representative formal proofs for the Principia pilot

This file formalizes the elementary metric content of the observational-
equivalence theorem in `papers/latex/empirical-limits.tex`.  It deliberately
does not encode empirical realization as a theorem: the only inputs here are
the explicitly displayed distance and tolerance.
-/

namespace Principia

/-- The fragment of a pseudometric used by the paper's tolerance argument. -/
structure PseudoDistance (α : Type) where
  dist : α → α → Nat
  self : ∀ x, dist x x = 0
  symm : ∀ x y, dist x y = dist y x
  triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

/-- Two models are observationally close at tolerance `ε`. -/
def CloseAt {α : Type} (d : PseudoDistance α) (ε : Nat) (x y : α) : Prop :=
  d.dist x y ≤ ε

theorem closeAt_refl {α : Type} (d : PseudoDistance α) (ε : Nat) (x : α) :
    CloseAt d ε x x := by
  simp [CloseAt, d.self]

theorem closeAt_symm {α : Type} (d : PseudoDistance α) (ε : Nat) {x y : α}
    (h : CloseAt d ε x y) : CloseAt d ε y x := by
  simpa [CloseAt, d.symm x y] using h

/-- If the distance takes no value in the half-open interval `(ε, 2 * ε]`,
then closeness at tolerance `ε` is transitive. -/
theorem closeAt_trans_of_gap {α : Type} (d : PseudoDistance α) (ε : Nat)
    (gap : ∀ x z, d.dist x z ≤ 2 * ε → d.dist x z ≤ ε)
    {x y z : α} (hxy : CloseAt d ε x y) (hyz : CloseAt d ε y z) :
    CloseAt d ε x z := by
  apply gap x z
  calc
    d.dist x z ≤ d.dist x y + d.dist y z := d.triangle x y z
    _ ≤ ε + ε := Nat.add_le_add hxy hyz
    _ = 2 * ε := by omega

/-! ## The explicit free-fall witness

Gravity parameters are recorded in tenths of `m s⁻²`; distances are recorded
in tenths of a metre.  At `T = 2 s`, the paper's formula
`d(M_g, M_g') = (T² / 2) |g - g'|` becomes twice the parameter difference.
-/

abbrev GravityModel := Nat

def natDistance (a b : Nat) : Nat :=
  max a b - min a b

theorem natDistance_comm (a b : Nat) : natDistance a b = natDistance b a := by
  simp [natDistance, Nat.max_comm, Nat.min_comm]

def gravityDistance (g g' : GravityModel) : Nat :=
  2 * natDistance g g'

def GravityClose (ε : Nat) (g g' : GravityModel) : Prop :=
  gravityDistance g g' ≤ ε

theorem gravity_close_refl (ε g : Nat) : GravityClose ε g g := by
  simp [GravityClose, gravityDistance, natDistance]

theorem gravity_close_symm (ε g g' : Nat) :
    GravityClose ε g g' ↔ GravityClose ε g' g := by
  simp [GravityClose, gravityDistance, natDistance_comm g g']

/-- The models `g = 9.8`, `9.9`, and `10.0 m s⁻²` at tolerance `0.2 m`
give a concrete failure of transitivity. -/
theorem gravity_close_not_transitive :
    GravityClose 2 98 99 ∧
    GravityClose 2 99 100 ∧
    ¬ GravityClose 2 98 100 := by
  simp [GravityClose, gravityDistance, natDistance]

/-- Consequently, there is no proof that `GravityClose 2` is transitive. -/
theorem gravity_close_is_not_transitive :
    ¬ (∀ x y z, GravityClose 2 x y → GravityClose 2 y z →
      GravityClose 2 x z) := by
  intro h
  have witness := gravity_close_not_transitive
  exact witness.2.2 (h 98 99 100 witness.1 witness.2.1)

end Principia
