/-
PRINCIPIA PHYSICA formal companion.
Lean-core formalization: no Mathlib and no differential geometry.
Theorems below establish finite algebraic and bookkeeping claims only.
-/

namespace Principia

inductive Label where
  | definition
  | axiom
  | assumption
  | conjecture
  | lemma
  | proposition
  | theorem
  | corollary
  | interpretation
  | empiricalStatement
  | establishedPhysicalResult
  | newResult
  deriving DecidableEq, Repr

structure Claim where
  ident : String
  label : Label
  deps : List String
  deriving Repr

/- S-P1: a finite shadow of the corrected, non-injective translation. -/
inductive Component where
  | k | d | i | e | p | a
  deriving DecidableEq, Repr

inductive SourceNotion where
  | kinematicProduct
  | observableEmbedding
  | dynamicalFactorization
  | portObservable
  | preparationDistribution
  | measurementKernel
  | adequacyRule
  deriving DecidableEq, Repr

def translate : SourceNotion → Component
  | .kinematicProduct => .k
  | .observableEmbedding => .k
  | .dynamicalFactorization => .d
  | .portObservable => .i
  | .preparationDistribution => .e
  | .measurementKernel => .e
  | .adequacyRule => .a

theorem translation_not_injective :
    ∃ x y, x ≠ y ∧ translate x = translate y := by
  refine ⟨.kinematicProduct, .observableEmbedding, ?_, rfl⟩
  decide

/- S-N1: exact classification for a scalar coupling shadow. -/
inductive CouplingClass where
  | decoupled
  | reciprocalCoupled
  | nonReciprocal
  deriving DecidableEq, Repr

def classifyScalar (c12 c21 : Int) : CouplingClass :=
  if c12 = 0 ∧ c21 = 0 then .decoupled
  else if c12 = c21 then .reciprocalCoupled
  else .nonReciprocal

theorem zero_is_decoupled : classifyScalar 0 0 = .decoupled := by
  decide

theorem nonzero_reciprocal_example :
    classifyScalar 3 3 = .reciprocalCoupled := by
  decide

theorem nonreciprocal_example :
    classifyScalar 3 2 = .nonReciprocal := by
  decide

/- S-N2: a carrier bijection alone does not preserve readings. -/
def IsBijection {X Y : Type} (f : X → Y) : Prop :=
  ∃ g : Y → X, (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)

theorem bijection_does_not_force_equal_readings :
    ∃ (f : Nat → Nat) (r₁ r₂ : Nat → Nat),
      IsBijection f ∧ r₁ 1 ≠ r₂ (f 1) := by
  refine ⟨fun x => x, fun x => x, fun x => 2 * x, ?_, ?_⟩
  · exact ⟨fun x => x, (fun _ => rfl), (fun _ => rfl)⟩
  · decide

/- S-N3: a finite algebraic shadow of retaining the same interaction datum. -/
structure QuadraticHamiltonian where
  kinetic : Int
  restoring : Int
  interaction : Int
  deriving DecidableEq, Repr

def compositeBeforeLimit (kappa : Int) : QuadraticHamiltonian :=
  ⟨1, 0, kappa⟩

def compositeAfterFactorLimits (kappa : Int) : QuadraticHamiltonian :=
  ⟨1, 0, kappa⟩

def compositeAfterDiscardingInterface : QuadraticHamiltonian :=
  ⟨1, 0, 0⟩

theorem fixed_interface_commutes (kappa : Int) :
    compositeBeforeLimit kappa = compositeAfterFactorLimits kappa := by
  rfl

theorem discarded_interface_can_differ :
    compositeBeforeLimit 1 ≠ compositeAfterDiscardingInterface := by
  decide

/- Dependency registry. This checks syntax, not mathematical truth. -/
def registry : List Claim :=
  [ ⟨"S-A1", .assumption, []⟩
  , ⟨"S-A2", .axiom, []⟩
  , ⟨"S-I1", .interpretation, ["S-A2"]⟩
  , ⟨"S-D1", .definition, ["S-A1"]⟩
  , ⟨"S-P1", .proposition, ["S-D1"]⟩
  , ⟨"S-L1", .lemma, ["S-D1"]⟩
  , ⟨"S-N1", .newResult, ["S-D1", "S-L1"]⟩
  , ⟨"S-C1", .corollary, ["S-N1"]⟩
  , ⟨"S-N2", .newResult, ["S-D1", "S-P1"]⟩
  , ⟨"S-I2", .interpretation, ["S-N2"]⟩
  , ⟨"S-N3", .newResult, ["S-D1"]⟩
  , ⟨"S-E2", .empiricalStatement, ["S-N3"]⟩
  , ⟨"S-E3", .empiricalStatement, []⟩
  , ⟨"S-C3", .conjecture, ["S-N1", "S-N2", "S-N3"]⟩
  ]

def declared (claims : List Claim) : List String :=
  claims.map Claim.ident

def wellFormed (claims : List Claim) : Bool :=
  claims.all fun claim =>
    claim.deps.all fun dep => (declared claims).contains dep

theorem registry_well_formed : wellFormed registry = true := by
  decide

end Principia
