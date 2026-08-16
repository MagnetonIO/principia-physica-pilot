/-
  Proofs.lean
  Machine-checked fragments accompanying
  "Empirical Realization of Compositional Structure: A Synthesis of the
   PRINCIPIA PHYSICA Topic Series".

  Lean 4 core only.  No Mathlib dependency.

  EPISTEMIC STATUS.  Every declaration in this file is a mathematical
  statement about definitions introduced in this file.  Nothing here
  asserts, or is capable of asserting, that any model is physically
  realized.  Realization enters only as a *parameter*: a tested set, an
  observation operator, a tolerance.  The file is therefore a formalization
  of the admissibility side of the treatise thesis, and of the precise
  points at which the admissibility side stops.

  Section map (numbers refer to papers/drafts/synthesis.tex):
    1.  Identifiability and identifiability up to a gauge      (Def. 2.5-2.6)
    2.  Records, record congruence, the kernel theorem         (Thm. 3.2)
    3.  Gauge freedom: kernel of a difference operator         (Prop. 4.4)
    4.  Compatibility regions and monotonicity                 (Prop. 2.8)
    5.  Propagation of tolerance through composition           (Lem. 7.1)
    6.  Process theories, models, substitution                 (Lem. 2.2)
    7.  Admissibility is not realization                       (Interp. 8.1)
-/

namespace Principia

/-! ###########################################################################
    ## 1.  Observation operators and identifiability
    ########################################################################### -/

/-- A model class `M` is *identifiable* under the observation operator
`O : M → D` when the record determines the model.  This is injectivity of `O`,
stated separately because in the treatise `O` carries the empirical content
(which experiments were run) while `M` carries the mathematical content. -/
def Identifiable {M D : Type} (O : M → D) : Prop :=
  ∀ m n : M, O m = O n → m = n

/-- Identifiability *up to* an equivalence `R`.  This is the form that actually
occurs in physics: the record fixes a gauge orbit, not a representative. -/
def IdentifiableUpTo {M D : Type} (O : M → D) (R : M → M → Prop) : Prop :=
  ∀ m n : M, O m = O n → R m n

/-- Identifiability is the special case in which the gauge group is trivial. -/
theorem identifiableUpTo_eq_iff {M D : Type} (O : M → D) :
    IdentifiableUpTo O (fun a b => a = b) ↔ Identifiable O := Iff.rfl

/-- A single confusion refutes identifiability.  This is the schema of every
underdetermination argument in the series. -/
theorem not_identifiable_of_confusion {M D : Type} (O : M → D)
    {m n : M} (hobs : O m = O n) (hne : m ≠ n) : ¬ Identifiable O := by
  intro hid
  exact hne (hid m n hobs)

/-! ###########################################################################
    ## 2.  Records on a tested set, and the kernel theorem
    ########################################################################### -/

/-- The record produced by evaluating an integer-valued model on a finite list
of tested inputs.  `T` is the tested set; everything outside `T` is untested by
construction, which is the whole point. -/
def record {X : Type} (T : List X) (m : X → Int) : List Int := T.map m

/-- Models agreeing pointwise on the tested set produce the same record. -/
theorem record_congr {X : Type} (m n : X → Int) :
    ∀ T : List X, (∀ x, x ∈ T → m x = n x) → record T m = record T n := by
  intro T
  induction T with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    have ha : m a = n a := h a (List.mem_cons.mpr (Or.inl rfl))
    have ht : record t m = record t n :=
      ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    show m a :: record t m = n a :: record t n
    rw [ha, ht]

/-- **Kernel theorem, finite-record form** (synthesis Thm. 3.2, discrete case).

A perturbation `h` that vanishes on the tested set leaves the record unchanged.
If `h` is nonzero anywhere, the perturbed model is a genuinely different model.
Hence the record does not identify the model.

This is the single mechanism behind claim C4 (Hamiltonians from finite
trajectory samples) and claim C5 (general finite-data underdetermination) of the
topic series: both are the statement that a *linear* observation operator has
nonzero kernel. -/
theorem underdetermined_of_vanishing_perturbation
    {X : Type} (T : List X) (m h : X → Int)
    (hvanish : ∀ x, x ∈ T → h x = 0)
    (x₀ : X) (hx₀ : h x₀ ≠ 0) :
    record T (fun x => m x + h x) = record T m ∧ (fun x => m x + h x) ≠ m := by
  constructor
  · refine record_congr _ _ T (fun x hx => ?_)
    have hz : h x = 0 := hvanish x hx
    show m x + h x = m x
    omega
  · intro hEq
    have hpt : m x₀ + h x₀ = m x₀ := congrFun hEq x₀
    exact hx₀ (by omega)

/-- Concretely: the zero model on `Nat`. -/
def m0 : Nat → Int := fun _ => 0

/-- A discrete "bump" supported entirely off the tested set `[0,1,2,3]`. -/
def bump7 : Nat → Int := fun n => if n = 7 then 1 else 0

/-- The perturbed model. -/
def m1 : Nat → Int := fun n => m0 n + bump7 n

theorem bump7_vanishes_on_tests : ∀ x, x ∈ [0, 1, 2, 3] → bump7 x = 0 := by
  decide

theorem records_agree : record [0, 1, 2, 3] m1 = record [0, 1, 2, 3] m0 := by
  decide

theorem models_differ_off_tests : m1 7 ≠ m0 7 := by
  decide

/-- The record operator on this tested set is not identifiable. -/
theorem record_not_identifiable :
    ¬ Identifiable (fun m : Nat → Int => record [0, 1, 2, 3] m) := by
  refine not_identifiable_of_confusion _ (m := m1) (n := m0) records_agree ?_
  intro hEq
  exact models_differ_off_tests (congrFun hEq 7)

/-! ###########################################################################
    ## 3.  Gauge freedom: the kernel of a difference operator is the constants
    ########################################################################### -/

/-- A discrete analogue of `H ↦ dH`: the forward difference.  The continuous
statement (a Hamiltonian is determined by its vector field up to an additive
constant on a connected manifold) is Prop. 4.4 of the synthesis; this is its
one-dimensional discrete shadow, proved here by induction. -/
def diff (H : Nat → Int) : Nat → Int := fun n => H (n + 1) - H n

/-- Additive constants are invisible to the difference operator: one half of
"identifiable exactly up to a constant". -/
theorem diff_shift (H : Nat → Int) (c : Int) :
    diff (fun n => H n + c) = diff H := by
  funext n
  show H (n + 1) + c - (H n + c) = H (n + 1) - H n
  omega

/-- Conversely, equal differences force agreement up to a *single* constant:
the kernel of `diff` contains nothing beyond the constants.  Together with
`diff_shift` this pins the gauge group exactly. -/
theorem eq_add_const_of_diff_eq (H K : Nat → Int) (hd : diff H = diff K) :
    ∀ n, K n = H n + (K 0 - H 0) := by
  intro n
  induction n with
  | zero =>
    show K 0 = H 0 + (K 0 - H 0)
    omega
  | succ k ih =>
    have hstep : H (k + 1) - H k = K (k + 1) - K k := congrFun hd k
    show K (k + 1) = H (k + 1) + (K 0 - H 0)
    omega

/-- The difference operator is identifiable exactly up to an additive constant.
The empirical content of `H` is its orbit under the additive group, not `H`. -/
theorem diff_identifiableUpTo_const :
    IdentifiableUpTo diff (fun H K => ∃ c : Int, ∀ n, K n = H n + c) := by
  intro H K hd
  exact ⟨K 0 - H 0, eq_add_const_of_diff_eq H K hd⟩

/-- And it is *not* identifiable on the nose: the gauge orbit is nontrivial. -/
theorem diff_not_identifiable : ¬ Identifiable diff := by
  refine not_identifiable_of_confusion diff
    (m := fun n => (n : Int)) (n := fun n => (n : Int) + 1) ?_ ?_
  · funext n
    show (↑(n + 1) : Int) - ↑n = (↑(n + 1) + 1 : Int) - (↑n + 1)
    omega
  · intro hEq
    have h0 : ((0 : Nat) : Int) = ((0 : Nat) : Int) + 1 := congrFun hEq 0
    omega

/-! ###########################################################################
    ## 4.  Compatibility regions and monotonicity
    ########################################################################### -/

/-- `a` and `b` differ by at most `e`, stated two-sidedly so that all reasoning
below is linear integer arithmetic. -/
def Within (e : Int) (a b : Int) : Prop := -e ≤ a - b ∧ a - b ≤ e

/-- A model is compatible with a record at tolerance `δ` when it fits every
tested input to within `δ`.  Compatibility is weaker than truth: the
compatibility region generally contains mutually incompatible extrapolations,
which is exactly `record_not_identifiable` above. -/
def Compatible {X : Type} (T : List X) (δ : Int) (obs m : X → Int) : Prop :=
  ∀ x, x ∈ T → Within δ (m x) (obs x)

/-- Loosening the tolerance can only enlarge the compatibility region. -/
theorem compatible_mono_tol {X : Type} (T : List X) (δ δ' : Int) (obs m : X → Int)
    (hδ : δ ≤ δ') (hc : Compatible T δ obs m) : Compatible T δ' obs m := by
  intro x hx
  obtain ⟨h1, h2⟩ := hc x hx
  exact ⟨by omega, by omega⟩

/-- Shrinking the tested set can only enlarge the compatibility region. -/
theorem compatible_mono_tests {X : Type} (T T' : List X) (δ : Int) (obs m : X → Int)
    (hsub : ∀ x, x ∈ T' → x ∈ T) (hc : Compatible T δ obs m) :
    Compatible T' δ obs m :=
  fun x hx => hc x (hsub x hx)

/-! ###########################################################################
    ## 5.  Propagation of tolerance through composition
    ########################################################################### -/

/-- Tolerances add along a chain. -/
theorem within_trans (a b c e₁ e₂ : Int)
    (h₁ : Within e₁ a b) (h₂ : Within e₂ b c) : Within (e₁ + e₂) a c := by
  obtain ⟨p, q⟩ := h₁
  obtain ⟨r, s⟩ := h₂
  exact ⟨by omega, by omega⟩

/-- **Composition bound** (synthesis Lem. 7.1, integer case).

If the inner components agree to `e₁`, the outer map carries scale `e₁` to
scale `d` (a modulus of continuity; in the Lipschitz case `d = L * e₁`), and
the outer components agree to `e₂`, then the composites agree to `d + e₂`.

Note what this does *not* say.  It bounds the discrepancy between two
deterministic composites.  It says nothing about joint statistics of the
components, which componentwise data does not determine at all (synthesis
Prop. 7.4).  The gap between the two is the assumption of compositional
closure, which is empirical. -/
theorem within_comp {X : Type}
    (f₁ g₁ : X → Int) (f₂ g₂ : Int → Int) (e₁ e₂ d : Int)
    (hmod : ∀ a b : Int, Within e₁ a b → Within d (f₂ a) (f₂ b))
    (h₁ : ∀ x, Within e₁ (f₁ x) (g₁ x))
    (h₂ : ∀ b, Within e₂ (f₂ b) (g₂ b))
    (x : X) : Within (d + e₂) (f₂ (f₁ x)) (g₂ (g₁ x)) :=
  within_trans _ _ _ d e₂ (hmod (f₁ x) (g₁ x) (h₁ x)) (h₂ (g₁ x))

/-! ###########################################################################
    ## 6.  Process theories, models, and the substitution lemma
    ########################################################################### -/

/-- The sequential fragment of an interface theory.  Only what the substitution
lemma actually uses is axiomatized; associativity and unit laws are not needed
and are therefore not assumed.  This is deliberate: the treatise distinguishes
the structure a theorem *uses* from the structure a formalism *offers*. -/
structure ProcessTheory where
  Obj  : Type
  Hom  : Obj → Obj → Type
  id   : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z

/-- A model is a composition-preserving assignment of mathematics to
interfaces.  This is the sequential shadow of the strong symmetric monoidal
functor of claim C1. -/
structure Model (E M : ProcessTheory) where
  onObj  : E.Obj → M.Obj
  onHom  : {X Y : E.Obj} → E.Hom X Y → M.Hom (onObj X) (onObj Y)
  onId   : ∀ X, onHom (E.id X) = M.id (onObj X)
  onComp : ∀ {X Y Z : E.Obj} (g : E.Hom Y Z) (f : E.Hom X Y),
             onHom (E.comp g f) = M.comp (onHom g) (onHom f)

/-- **Substitution.**  Equal processes have equal images in every sequential
context.  The proof is one rewrite: this is a theorem about the formalization,
not about physical indistinguishability. -/
theorem substitution {E M : ProcessTheory} (F : Model E M)
    {W X Y Z : E.Obj} (a : E.Hom W X) (e e' : E.Hom X Y) (b : E.Hom Y Z)
    (h : e = e') :
    F.onHom (E.comp b (E.comp e a)) = F.onHom (E.comp b (E.comp e' a)) := by
  rw [h]

/-- Functoriality rewrites the image of a context as the context of images. -/
theorem context_factorization {E M : ProcessTheory} (F : Model E M)
    {W X Y Z : E.Obj} (a : E.Hom W X) (e : E.Hom X Y) (b : E.Hom Y Z) :
    F.onHom (E.comp b (E.comp e a))
      = M.comp (F.onHom b) (M.comp (F.onHom e) (F.onHom a)) := by
  rw [F.onComp, F.onComp]

/-- Contextual invariance (synthesis Cor. 2.3): no sequential context separates
the images of processes identified in the interface theory. -/
theorem contextual_invariance {E M : ProcessTheory} (F : Model E M)
    {W X Y Z : E.Obj} (a : E.Hom W X) (e e' : E.Hom X Y) (b : E.Hom Y Z)
    (h : e = e') :
    M.comp (F.onHom b) (M.comp (F.onHom e) (F.onHom a))
      = M.comp (F.onHom b) (M.comp (F.onHom e') (F.onHom a)) := by
  rw [h]

/-! ###########################################################################
    ## 7.  Admissibility is not realization
    ########################################################################### -/

/-- Two models can both be admissible members of the class and produce the same
record, while disagreeing on an untested input.  No amount of further
mathematics inside the class removes the disagreement; only a new experiment
does.  This is the formal residue of Interpretation 8.1. -/
theorem admissibility_not_realization :
    ∃ m n : Nat → Int,
      record [0, 1, 2, 3] m = record [0, 1, 2, 3] n ∧ m 7 ≠ n 7 :=
  ⟨m1, m0, records_agree, models_differ_off_tests⟩

/-- The converse direction is *not* provable here and is not proved anywhere in
the series: nothing in this file entails that either `m1` or `m0` describes any
physical system.  That statement has no formal content in this language, which
is the point of separating the Lean development from the empirical sections of
the papers. -/
theorem no_realization_predicate_is_definable
    (Realized : (Nat → Int) → Prop)
    (hgauge : ∀ m n : Nat → Int,
      record [0, 1, 2, 3] m = record [0, 1, 2, 3] n → (Realized m ↔ Realized n)) :
    (Realized m1 ↔ Realized m0) :=
  hgauge m1 m0 records_agree

end Principia

/-
  Axiom audit.  These commands print the axiom dependencies of the main
  results; they are diagnostics, not claims.
-/
#print axioms Principia.underdetermined_of_vanishing_perturbation
#print axioms Principia.eq_add_const_of_diff_eq
#print axioms Principia.within_comp
#print axioms Principia.contextual_invariance
#print axioms Principia.admissibility_not_realization
