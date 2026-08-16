/-
  Proofs.lean
  PRINCIPIA PHYSICA -- formal appendix to
  "Compositional Realization, Hamiltonian Reconstruction, and Empirical Limits:
   a synthesis".

  SCOPE AND EPISTEMIC STATUS (read before using this file).

  What this file is: a machine-checked development of DISCRETE SURROGATES of
  six structural claims of the paper series.  Each theorem below is proved in
  Lean 4 core (no Mathlib and no proof placeholders or added axioms). The surrogate replaces a
  smooth manifold by a type, a symplectic form by nothing at all, a vector
  field by a step function, and de Rham cohomology of the circle by the
  telescoping sum of a periodic integer sequence.

  What this file is NOT: it is not a formalization of the smooth theorems of
  the series.  Nothing here mentions a manifold, a 2-form, or a flow.  A
  surrogate that checks does not certify the smooth statement; it certifies
  the combinatorial skeleton that the smooth proof specializes.  Where the
  correspondence is only an analogy we say so in the comment above the
  theorem, and Section 6 of the synthesis paper lists what is lost.

  Correspondence table (surrogate  |->  smooth claim in the series):
    par / runPar          |-> CS-P1, HR prop-product-well-typed  (product is
                              well typed and the composite run factors)
    par_nonInteracting,
    coupled_not_par       |-> HR new-interaction-outside-tensor  (interaction
                              is outside the range of the monoidal product)
    separable_iff_noMixedDifference
                          |-> CS-N1 separation equivalence       (split
                              dynamics iff additively separable generator)
    d_add_const,
    d_determines_upto_const
                          |-> HR cor-underdetermination          (generator
                              determined up to an additive constant)
    cycle_sum_zero_of_potential,
    potential_of_cycle_sum_zero,
    no_potential_on_cycle |-> HR thm-exact-sequence, nonex-torus (a closed
                              form with nonzero period has no global potential)
    identifiable_iff_factors
                          |-> EL C2 / observational quotient     (a property
                              is identifiable iff it factors through the
                              observational quotient)

  Toolchain: Lean (version 4.33.0).  Build: `lean Proofs.lean` (no imports).
-/

namespace Principia

/-! ############################################################
    ## 1.  Typed deterministic systems and parallel composition
    ############################################################

    Surrogate for the compositional layer of the series.  A system is a
    step map and a readout; the symplectic structure of the smooth papers
    has NO counterpart here, which is exactly why nothing below can be read
    as a statement about Hamiltonian mechanics. -/

structure Sys (I S O : Type) where
  step : I → S → S
  read : S → O

/-- Parallel (monoidal) product: independent inputs, independent states. -/
def par {I₁ S₁ O₁ I₂ S₂ O₂ : Type}
    (a : Sys I₁ S₁ O₁) (b : Sys I₂ S₂ O₂) :
    Sys (I₁ × I₂) (S₁ × S₂) (O₁ × O₂) where
  step := fun i x => (a.step i.1 x.1, b.step i.2 x.2)
  read := fun x => (a.read x.1, b.read x.2)

/-- Serial composition with the synchronous convention: the second component
    reads the *updated* output of the first. -/
def serial {I S O T P : Type} (a : Sys I S O) (b : Sys O T P) :
    Sys I (S × T) P where
  step := fun i x =>
    let s' := a.step i x.1
    (s', b.step (a.read s') x.2)
  read := fun x => b.read x.2

/-- Iterate a system along a finite input word. -/
def run {I S O : Type} (a : Sys I S O) : List I → S → S
  | [], x => x
  | i :: is, x => run a is (a.step i x)

/-- The run of a product is the pair of the runs: the monoidal product does
    not create dependence between the factors.  Surrogate of CS-P1 and of
    HR prop-product-well-typed. -/
theorem runPar {I₁ S₁ O₁ I₂ S₂ O₂ : Type}
    (a : Sys I₁ S₁ O₁) (b : Sys I₂ S₂ O₂) :
    ∀ (is : List (I₁ × I₂)) (x : S₁) (y : S₂),
      run (par a b) is (x, y)
        = (run a (is.map Prod.fst) x, run b (is.map Prod.snd) y) := by
  intro is
  induction is with
  | nil => intro x y; rfl
  | cons i is ih => intro x y; simpa [run, par] using ih (a.step i.1 x) (b.step i.2 y)

/-- Symmetry (braiding) at the level of runs. -/
theorem runPar_swap {I₁ S₁ O₁ I₂ S₂ O₂ : Type}
    (a : Sys I₁ S₁ O₁) (b : Sys I₂ S₂ O₂)
    (is : List (I₁ × I₂)) (x : S₁) (y : S₂) :
    run (par b a) (is.map Prod.swap) (y, x)
      = Prod.swap (run (par a b) is (x, y)) := by
  rw [runPar, runPar]
  simp [List.map_map, Function.comp_def]

/-! ############################################################
    ## 2.  Interaction is outside the range of the product
    ############################################################ -/

/-- A system on a product state space is *non-interacting* when the next
    state of each factor is independent of the other factor's state. -/
def NonInteracting {I₁ S₁ I₂ S₂ O : Type}
    (s : Sys (I₁ × I₂) (S₁ × S₂) O) : Prop :=
  (∀ i x y y', (s.step i (x, y)).1 = (s.step i (x, y')).1) ∧
  (∀ i x x' y, (s.step i (x, y)).2 = (s.step i (x', y)).2)

theorem par_nonInteracting {I₁ S₁ O₁ I₂ S₂ O₂ : Type}
    (a : Sys I₁ S₁ O₁) (b : Sys I₂ S₂ O₂) : NonInteracting (par a b) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- An explicitly coupled system on the same product state space. -/
def coupled : Sys (Unit × Unit) (Int × Int) (Int × Int) where
  step := fun _ x => (x.1 + x.2, x.2)
  read := fun x => x

theorem coupled_interacts : ¬ NonInteracting coupled := by
  intro h
  have h0 : ((coupled.step ((), ()) (0, 0)).1) = ((coupled.step ((), ()) (0, 1)).1) :=
    h.1 ((), ()) 0 0 1
  simp [coupled] at h0

/-- Surrogate of HR new-interaction-outside-tensor: a coupled system is not
    equal to any parallel product, so `par` alone cannot express interaction.
    The smooth theorem is sharper -- it characterises the image of the
    monoidal product by local constancy of the coupling term -- and is NOT
    proved here. -/
theorem coupled_not_par :
    ¬ ∃ (a b : Sys Unit Int Int), coupled = par a b := by
  intro h
  match h with
  | ⟨a, b, hab⟩ =>
      exact coupled_interacts (hab ▸ par_nonInteracting a b)

/-! ############################################################
    ## 3.  Separation equivalence (surrogate of CS-N1)
    ############################################################

    In the smooth paper, a Hamiltonian vector field on a connected product
    splits componentwise iff the generator is additively separable up to a
    constant.  The combinatorial content of "additively separable" is the
    vanishing of the mixed second difference, and that is what is proved
    here.  No dynamics is involved. -/

def Separable {α β : Type} (V : α → β → Int) : Prop :=
  ∃ f : α → Int, ∃ g : β → Int, ∀ a b, V a b = f a + g b

def NoMixedDifference {α β : Type} (V : α → β → Int) : Prop :=
  ∀ a a' b b', V a b + V a' b' = V a b' + V a' b

theorem separable_iff_noMixedDifference {α β : Type}
    (V : α → β → Int) (a₀ : α) (b₀ : β) :
    Separable V ↔ NoMixedDifference V := by
  constructor
  · intro hsep a a' b b'
    match hsep with
    | ⟨f, g, hV⟩ => simp [hV]; omega
  · intro hmix
    refine ⟨fun a => V a b₀, fun b => V a₀ b - V a₀ b₀, ?_⟩
    intro a b
    have h := hmix a a₀ b b₀
    show V a b = V a b₀ + (V a₀ b - V a₀ b₀)
    omega

/-- A concrete interacting coupling: `V a b = a * b` is not separable.  This
    is the discrete counterpart of the interaction potential in the
    coupled-oscillator counterexample of the compositional-systems paper. -/
theorem mul_not_separable : ¬ Separable (fun a b : Int => a * b) := by
  intro h
  have hmix := (separable_iff_noMixedDifference (fun a b : Int => a * b) 0 0).mp h
  have := hmix 0 1 0 1
  simp at this

/-! ############################################################
    ## 4.  The generator is determined up to an additive constant
    ############################################################

    Surrogate of HR cor-underdetermination.  `d` is the forward difference,
    standing in for the exterior derivative; a constant is invisible to it,
    and on the (connected) linear order that is the only ambiguity. -/

def d (H : Nat → Int) (n : Nat) : Int := H (n + 1) - H n

theorem d_add_const (H : Nat → Int) (c : Int) : d (fun n => H n + c) = d H := by
  funext n
  simp [d]
  omega

theorem d_determines_upto_const (H K : Nat → Int) (h : d H = d K) :
    ∀ n, H n - K n = H 0 - K 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      have hk : d H k = d K k := congrFun h k
      simp [d] at hk
      omega

/-- Consequently the additive constant is empirically idle for any readout
    that is a function of the difference alone. -/
theorem const_invisible (H : Nat → Int) (c : Int) (μ : (Nat → Int) → Prop)
    (hμ : ∀ F G, d F = d G → (μ F ↔ μ G)) :
    μ H ↔ μ (fun n => H n + c) :=
  (hμ H (fun n => H n + c) (d_add_const H c).symm)

/-! ############################################################
    ## 5.  Periods obstruct a global potential
    ############################################################

    Surrogate of HR thm-exact-sequence and of the torus non-example.  A
    "closed one-form" is a sequence `α : Nat → Int` that is `n`-periodic; a
    "global potential" is an `n`-periodic `H` with `H (k+1) - H k = α k`.
    The period of the form is the cycle sum `psum α n`, and it is the exact
    obstruction.  The de Rham cohomology of the smooth statement is replaced
    by this single integer. -/

def psum (α : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => psum α n + α n

def Periodic (n : Nat) (f : Nat → Int) : Prop := ∀ k, f (k + n) = f k

theorem psum_telescope (α H : Nat → Int) (h : ∀ k, H (k + 1) - H k = α k) :
    ∀ m, psum α m = H m - H 0 := by
  intro m
  induction m with
  | zero =>
      have hz : psum α 0 = 0 := rfl
      omega
  | succ k ih =>
      have hk := h k
      have hs : psum α (k + 1) = psum α k + α k := rfl
      omega

/-- Necessity: a global potential forces the period to vanish. -/
theorem cycle_sum_zero_of_potential (n : Nat) (α H : Nat → Int)
    (h : ∀ k, H (k + 1) - H k = α k) (hper : Periodic n H) :
    psum α n = 0 := by
  have h1 : psum α n = H n - H 0 := psum_telescope α H h n
  have h2 : H (0 + n) = H 0 := hper 0
  have h3 : (0 : Nat) + n = n := Nat.zero_add n
  rw [h3] at h2
  omega

/-- Sufficiency: if the period vanishes, the partial-sum sequence is a
    global potential. -/
theorem potential_of_cycle_sum_zero (n : Nat) (α : Nat → Int)
    (hα : Periodic n α) (h0 : psum α n = 0) :
    (∀ k, psum α (k + 1) - psum α k = α k) ∧ Periodic n (psum α) := by
  constructor
  · intro k
    have hs : psum α (k + 1) = psum α k + α k := rfl
    omega
  · intro k
    induction k with
    | zero =>
        have hz : (0 : Nat) + n = n := Nat.zero_add n
        rw [hz]
        exact h0
    | succ j ih =>
        have hshift : j + 1 + n = (j + n) + 1 := by omega
        have hαj : α (j + n) = α j := hα j
        rw [hshift]
        simp [psum, ih, hαj]

/-- Nonvacuity: the constant form `1` on an `n`-cycle with `n > 0` has period
    `n ≠ 0`, hence no global potential.  Discrete counterpart of
    `ι_X ω = dθ²` on the 2-torus. -/
theorem psum_one : ∀ n : Nat, psum (fun _ => 1) n = (n : Int) := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      have hs : psum (fun _ => (1 : Int)) (k + 1) = psum (fun _ => (1 : Int)) k + 1 := rfl
      omega

theorem no_potential_on_cycle (n : Nat) (hn : 0 < n) :
    ¬ ∃ H : Nat → Int, (∀ k, H (k + 1) - H k = 1) ∧ Periodic n H := by
  intro h
  match h with
  | ⟨H, hH, hper⟩ =>
      have hz : psum (fun _ => 1) n = 0 :=
        cycle_sum_zero_of_potential n (fun _ => 1) H hH hper
      have : (n : Int) = 0 := by rw [← psum_one n]; exact hz
      omega

/-! ############################################################
    ## 6.  Observational equivalence and identifiability
    ############################################################

    Surrogate of the empirical-limits layer.  Outcome laws are replaced by
    values in an arbitrary type `O`; total variation, tolerances and the
    error budget of the paper have NO counterpart here, so nothing below
    says anything about statistical identification from finite data. -/

structure Experiments (M C O : Type) where
  law : C → M → O

def obsEq {M C O : Type} (E : Experiments M C O) (m m' : M) : Prop :=
  ∀ c, E.law c m = E.law c m'

theorem obsEq_equivalence {M C O : Type} (E : Experiments M C O) :
    Equivalence (obsEq E) where
  refl _ := fun _ => rfl
  symm h := fun c => (h c).symm
  trans h h' := fun c => (h c).trans (h' c)

def obsSetoid {M C O : Type} (E : Experiments M C O) : Setoid M :=
  ⟨obsEq E, obsEq_equivalence E⟩

/-- Restriction monotonicity: reindexing the context set along any map cannot
    separate models that the larger family already failed to separate.
    Surrogate of the EL restriction lemma. -/
theorem obsEq_reindex {M C C' O : Type} (E : Experiments M C O)
    (f : C' → C) (m m' : M) (h : obsEq E m m') :
    obsEq (Experiments.mk (fun c' => E.law (f c'))) m m' :=
  fun c' => h (f c')

def Identifiable {M C O Z : Type} (E : Experiments M C O) (φ : M → Z) : Prop :=
  ∀ m m', obsEq E m m' → φ m = φ m'

/-- A property is identifiable exactly when it factors through the
    observational quotient.  Surrogate of EL C2 and of the factorization
    limit; the smooth/statistical paper states it for probability laws. -/
theorem identifiable_iff_factors {M C O Z : Type}
    (E : Experiments M C O) (φ : M → Z) :
    Identifiable E φ ↔
      ∃ ψ : Quotient (obsSetoid E) → Z,
        ∀ m, φ m = ψ (Quotient.mk (obsSetoid E) m) := by
  constructor
  · intro hid
    exact ⟨Quotient.lift φ hid, fun _ => rfl⟩
  · intro hfac m m' hmm
    match hfac with
    | ⟨ψ, hψ⟩ =>
        have : Quotient.mk (obsSetoid E) m = Quotient.mk (obsSetoid E) m' :=
          Quotient.sound hmm
        rw [hψ m, hψ m', this]

/-- No decision rule reading only the registered outcome laws can separate
    observationally equivalent models.  Surrogate of the EL corollary. -/
theorem no_rule_separates {M C O : Type} (E : Experiments M C O)
    (rule : (C → O) → Bool) (m m' : M) (h : obsEq E m m') :
    rule (fun c => E.law c m) = rule (fun c => E.law c m') := by
  have : (fun c => E.law c m) = (fun c => E.law c m') := funext h
  rw [this]

end Principia
