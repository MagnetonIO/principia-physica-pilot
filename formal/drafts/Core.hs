-- |
-- Module      : Core
-- Description : Executable companion to the PRINCIPIA PHYSICA synthesis paper
--
-- PRINCIPIA PHYSICA -- formal/drafts/Core.hs
--
-- Representative Haskell draft accompanying the synthesis paper
-- \"Layered Composition, Reciprocity, and Protocol-Relative Realization\".
--
-- SCOPE AND HONEST LIMITS OF THIS FILE.
--
-- Nothing in this file is a proof.  Every function below is either
--
--   (a) a /decision procedure/ for a condition that the paper states
--       algebraically (reciprocity, separability, coupling class), or
--   (b) a /numerical witness/ that exhibits, at stated finite precision and
--       on a stated finite grid, the behaviour asserted by a counterexample
--       in the paper.
--
-- A numerical witness can refute a universal claim only up to the declared
-- tolerance, and can never establish one.  The tolerances used by @main@ are
-- declared explicitly in 'tolStrict' and 'tolLoose' and are reported in the
-- output so that a reader can reproduce or contest them.
--
-- Claim identifiers in comments refer to the synthesis paper:
-- CS = compositional-systems, HR = hamiltonian-reconstruction,
-- EL = empirical-limits, S = synthesis.
--
-- Verified against: GHC 8.4.2, @base@ only, no external dependencies.
-- Build: @ghc -Wall -main-is Core Core.hs -o core@

{-# LANGUAGE ScopedTypeVariables #-}

module Core
  ( -- * Epistemic bookkeeping
    Label(..), Claim(..), registry, registryWellFormed, registryNoFreeProofs
    -- * Typed systems, processes, composition (CS-D1, CS-D3, CS-D5)
  , Sys(..), Proc(..), idProc, compProc, parSys, parProc, projL, projR
  , coherentOn
    -- * Linear algebra
  , Matrix, transposeM, subM, frobenius, zeroM
    -- * Reciprocity and the coupling trichotomy (HR-N1, S-N1)
  , CouplingClass(..), reciprocityDefect, isReciprocal, classifyCoupling
  , splitInvariantScalar
    -- * Dynamics
  , Params(..), vectorField, rk4Step, integrate, divergenceLinear
  , factorizationResidual
    -- * Empirical layer (EL-D1, EL-D2, EL-P3, EL-P4, EL-N2, S-N2, S-N3)
  , obsEquivExact, obsEquivTol, transitivityWitness
  , portReading, transportAlpha, transportedHamiltonianResidual
  , limitNonCommutation, oscillatorFreeLimitGap
  , kineticRelativistic, kineticNewtonian, newtonianGapOn
  , sampleAmbiguity
    -- * Entry point
  , main
  ) where

import           Data.List   (intercalate, transpose)
import           System.Exit (exitFailure, exitSuccess)
import           Text.Printf (printf)

-- ---------------------------------------------------------------------------
-- 0. Epistemic bookkeeping
-- ---------------------------------------------------------------------------

-- | The twelve labels admitted by the pilot epistemic contract.  Reifying
-- them lets the registry below be checked mechanically for bookkeeping
-- errors.  It does not and cannot check that a claim is true.
data Label
  = Definition
  | Axiom
  | Assumption
  | Conjecture
  | Lemma
  | Proposition
  | Theorem
  | Corollary
  | Interpretation
  | EmpiricalStatement
  | EstablishedPhysicalResult
  | NewResult
  deriving (Eq, Ord, Show, Enum, Bounded)

data Claim = Claim
  { claimId    :: String
  , claimLabel :: Label
  , claimDeps  :: [String]
  } deriving (Eq, Show)

-- | The synthesis paper's dependency graph, mirrored from @Proofs.lean@.
registry :: [Claim]
registry =
  [ Claim "S-A1" Assumption         []
  , Claim "S-A2" Axiom              []
  , Claim "S-E1" EmpiricalStatement []
  , Claim "S-I1" Interpretation     ["S-A2"]
  , Claim "S-D1" Definition         ["S-A1"]
  , Claim "S-P1" Proposition        ["S-D1"]
  , Claim "S-L1" Lemma              ["S-D1"]
  , Claim "S-N1" NewResult          ["S-D1", "S-L1"]
  , Claim "S-C1" Corollary          ["S-N1"]
  , Claim "S-P2" Proposition        ["S-N1"]
  , Claim "S-N2" NewResult          ["S-D1", "S-P1"]
  , Claim "S-I2" Interpretation     ["S-N2"]
  , Claim "S-C2" Corollary          ["S-N2"]
  , Claim "S-N3" NewResult          ["S-N1"]
  , Claim "S-E2" EmpiricalStatement []
  , Claim "S-E3" EmpiricalStatement []
  , Claim "S-C3" Conjecture         ["S-N1", "S-N2", "S-N3"]
  ]

-- | Every declared dependency names a declared claim.
registryWellFormed :: [Claim] -> Bool
registryWellFormed cs =
  all (\c -> all (`elem` ids) (claimDeps c)) cs
  where ids = map claimId cs

-- | Syntactic guard against the failure mode \"an assumption silently
-- promoted to a proved result\": nothing labelled as a proved claim may
-- have an empty dependency list.
registryNoFreeProofs :: [Claim] -> Bool
registryNoFreeProofs = all ok
  where
    ok c
      | claimLabel c `elem` [Lemma, Proposition, Theorem, Corollary] =
          not (null (claimDeps c))
      | otherwise = True

-- ---------------------------------------------------------------------------
-- 1. Typed systems and processes  (CS-D1, CS-D3, CS-A2, CS-P1, CS-D5)
-- ---------------------------------------------------------------------------

-- | A system keeps states and observables as separate types, joined only by
-- an evaluation map.  This is CS-D1 with the algebra structure dropped: we
-- retain only what the executable checks below actually use.
newtype Sys st obs v = Sys { evalObs :: obs -> st -> v }

-- | A typed process: a forward map on states together with a pullback on
-- observables (CS-D3).  The coherence condition of CS-D3 is /not/ enforced
-- by the type system; it is checked on finite samples by 'coherentOn'.
data Proc sa oa sb ob = Proc
  { procFwd  :: sa -> sb
  , procPull :: ob -> oa
  }

idProc :: Proc s o s o
idProc = Proc id id

-- | Note the contravariance of the observable component: this is exactly the
-- step used in the proof of CS-P1.
compProc :: Proc a oa b ob -> Proc b ob c oc -> Proc a oa c oc
compProc f g = Proc (procFwd g . procFwd f) (procPull f . procPull g)

-- | Kinematical parallel composition (CS-D5), with observables of the
-- composite modelled by the disjoint union of factor observables.
parSys :: Sys s1 o1 v -> Sys s2 o2 v -> Sys (s1, s2) (Either o1 o2) v
parSys a b = Sys $ \o (x, y) -> case o of
  Left  oa -> evalObs a oa x
  Right ob -> evalObs b ob y

parProc :: Proc a oa b ob -> Proc c oc d od
        -> Proc (a, c) (Either oa oc) (b, d) (Either ob od)
parProc f g = Proc
  (\(x, y) -> (procFwd f x, procFwd g y))
  (\o -> case o of
      Left  ob -> Left  (procPull f ob)
      Right od -> Right (procPull g od))

projL :: Proc (a, b) (Either oa ob) a oa
projL = Proc fst Left

projR :: Proc (a, b) (Either oa ob) b ob
projR = Proc snd Right

-- | Check the CS-D3 coherence equation on a finite sample of states and
-- observables.  A pass is evidence on that sample only.
coherentOn :: Eq v
           => Sys sa oa v -> Sys sb ob v -> Proc sa oa sb ob
           -> [sa] -> [ob] -> Bool
coherentOn sa sb p xs os =
  and [ evalObs sb o (procFwd p x) == evalObs sa (procPull p o) x
      | x <- xs, o <- os ]

-- ---------------------------------------------------------------------------
-- 2. Linear algebra
-- ---------------------------------------------------------------------------

type Matrix = [[Double]]

transposeM :: Matrix -> Matrix
transposeM = transpose

subM :: Matrix -> Matrix -> Matrix
subM = zipWith (zipWith (-))

frobenius :: Matrix -> Double
frobenius m = sqrt (sum [x * x | row <- m, x <- row])

zeroM :: Int -> Int -> Matrix
zeroM r c = replicate r (replicate c 0)

-- ---------------------------------------------------------------------------
-- 3. Reciprocity and the coupling trichotomy  (HR-N1, HR-N2, S-N1)
-- ---------------------------------------------------------------------------

-- | The three classes of linear interconnection isolated by S-N1.
data CouplingClass
  = Decoupled          -- ^ @C12 = C21 = 0@: the flow factorizes (CS-C1).
  | ReciprocalCoupled  -- ^ @C21 = C12^T /= 0@: Hamiltonian, not factorized.
  | NonReciprocal      -- ^ @C21 /= C12^T@: not Hamiltonian for @omega_+@.
  deriving (Eq, Show)

-- | The exterior derivative of @iota_Y omega_+@ has coefficient matrix
-- @C21^T - C12@ on the basis @dq_{1a} ^ dq_{2b}@ (the computation is carried
-- out in the paper).  Its vanishing is HR-N1's reciprocity condition.
reciprocityDefect :: Matrix -> Matrix -> Matrix
reciprocityDefect c12 c21 = subM (transposeM c21) c12

isReciprocal :: Double -> Matrix -> Matrix -> Bool
isReciprocal tol c12 c21 = frobenius (reciprocityDefect c12 c21) <= tol

classifyCoupling :: Double -> Matrix -> Matrix -> CouplingClass
classifyCoupling tol c12 c21
  | frobenius c12 <= tol && frobenius c21 <= tol = Decoupled
  | isReciprocal tol c12 c21                     = ReciprocalCoupled
  | otherwise                                    = NonReciprocal

-- | Scalar case of HR-N2: a split-respecting invariant form exists iff the
-- two couplings vanish together.  Returns the witness weights @(a1, a2)@
-- when one exists.
splitInvariantScalar :: Double -> Double -> Double -> Maybe (Double, Double)
splitInvariantScalar tol c12 c21
  | abs c12 <= tol && abs c21 <= tol = Just (1, 1)
  | abs c12 <= tol || abs c21 <= tol = Nothing
  | otherwise                        = Just (c21, c12)

-- ---------------------------------------------------------------------------
-- 4. Dynamics: two coupled one-degree-of-freedom oscillators
-- ---------------------------------------------------------------------------

-- | State order is @[q1, p1, q2, p2]@.
data Params = Params
  { pM1  :: Double
  , pK1  :: Double
  , pM2  :: Double
  , pK2  :: Double
  , pC12 :: Double
  , pC21 :: Double
  } deriving (Eq, Show)

vectorField :: Params -> [Double] -> [Double]
vectorField pr [q1, p1, q2, p2] =
  [ p1 / pM1 pr
  , negate (pK1 pr * q1) - pC12 pr * q2
  , p2 / pM2 pr
  , negate (pK2 pr * q2) - pC21 pr * q1
  ]
vectorField _ s = error ("vectorField: expected a 4-vector, got " ++ show (length s))

-- | The Jacobian of the linear field has zero diagonal, so its divergence
-- vanishes for every choice of couplings (HR-P3): Liouville volume is
-- preserved even when the symplectic form is not.
divergenceLinear :: Params -> Double
divergenceLinear _ = 0

rk4Step :: ([Double] -> [Double]) -> Double -> [Double] -> [Double]
rk4Step f h y = zipWith (+) y (map (* (h / 6)) increment)
  where
    k1 = f y
    k2 = f (axpy (h / 2) k1 y)
    k3 = f (axpy (h / 2) k2 y)
    k4 = f (axpy h k3 y)
    increment = foldr1 (zipWith (+)) [k1, map (* 2) k2, map (* 2) k3, k4]
    axpy a v w = zipWith (\vi wi -> wi + a * vi) v w

integrate :: ([Double] -> [Double]) -> Double -> Int -> [Double] -> [Double]
integrate f h n y0 = iterate (rk4Step f h) y0 !! n

-- | Compare the flow of the composite against the product of the flows of
-- the two isolated factors, at time @t = h * n@ (CS-T1, CS-C1).  A residual
-- at the level of integrator error is a witness /for/ factorization on this
-- grid; a large residual is a witness /against/ it.
factorizationResidual :: Params -> Double -> Int -> [Double] -> Double
factorizationResidual pr h n y0 =
  maximum (map abs (zipWith (-) joint split))
  where
    joint = integrate (vectorField pr) h n y0
    [q10, p10, q20, p20] = y0
    fac1 = integrate (vectorField pr { pC12 = 0, pC21 = 0, pM2 = 1, pK2 = 0 })
                     h n [q10, p10, 0, 0]
    fac2 = integrate (vectorField pr { pC12 = 0, pC21 = 0, pM1 = 1, pK1 = 0 })
                     h n [0, 0, q20, p20]
    split = [fac1 !! 0, fac1 !! 1, fac2 !! 2, fac2 !! 3]

-- ---------------------------------------------------------------------------
-- 5. Protocol layer  (EL-D1, EL-D2)
-- ---------------------------------------------------------------------------

-- | Exact protocol-relative observational equivalence over a finite index
-- set (EL-D2).  Finiteness is essential: this decides equivalence only for
-- the indices supplied.
obsEquivExact :: Eq o => [i] -> (i -> o) -> (i -> o) -> Bool
obsEquivExact idxs f g = all (\i -> f i == g i) idxs

-- | Tolerance version.  Returns the realised supremum distance alongside the
-- verdict so that the margin is visible rather than hidden.
obsEquivTol :: Double -> [i] -> (i -> Double) -> (i -> Double) -> (Bool, Double)
obsEquivTol eps idxs f g = (d <= eps, d)
  where d = maximum (0 : map (\i -> abs (f i - g i)) idxs)

-- | EL's counterexample to transitivity of approximate equivalence, as a
-- computed triple of verdicts @(A~B, B~C, A~C)@.
transitivityWitness :: Double -> (Bool, Bool, Bool)
transitivityWitness eps =
  ( fst (obsEquivTol eps [()] (const a) (const b))
  , fst (obsEquivTol eps [()] (const b) (const c))
  , fst (obsEquivTol eps [()] (const a) (const c))
  )
  where
    a = 0
    b = 0.75 * eps
    c = 1.50 * eps

-- ---------------------------------------------------------------------------
-- 6. Mathematical isomorphism versus protocol distinction  (HR-N3, S-N2)
-- ---------------------------------------------------------------------------

-- | Port reading @q(t)@ for @H_m = p^2/(2m) + m w0^2 q^2 / 2@ started at
-- @(q0, p0)@.
portReading :: Double -> Double -> Double -> Double -> Double -> Double
portReading m w0 q0 p0 t = q0 * cos (w0 * t) + (p0 / (m * w0)) * sin (w0 * t)

-- | The symplectic rescaling @(q,p) |-> (alpha q, p/alpha)@ carrying @H_m@
-- to @H_m'@ (HR-N3).
transportAlpha :: Double -> Double -> Double
transportAlpha m m' = sqrt (m / m')

-- | Residual of @H_m(q,p) - H_m'(F(q,p))@ under that rescaling.  Near zero
-- confirms that the two closed systems are isomorphic as Hamiltonian
-- systems; the port reading nevertheless differs, which is the content of
-- S-N2.
transportedHamiltonianResidual :: Double -> Double -> Double -> Double -> Double -> Double
transportedHamiltonianResidual m m' w0 q p = hm - hm'
  where
    alpha = transportAlpha m m'
    hm    = p * p / (2 * m)  + m  * w0 * w0 * q * q / 2
    hm'   = (p / alpha) ** 2 / (2 * m') + m' * w0 * w0 * (alpha * q) ** 2 / 2

-- ---------------------------------------------------------------------------
-- 7. Limits  (EL-P3, EL-P4, S-N3)
-- ---------------------------------------------------------------------------

-- | S-N3 witness.  Left component: the @w -> 0@ limit of the /composite/
-- with coupling @kappa@ retained.  Right component: the composite of the
-- @w -> 0@ limits of the /isolated/ factors, which carries no coupling
-- because (CS-P4) the interaction is not determined by the factors.
-- The returned pair is @(q1 from the limit of the composite, q1 from the
-- composite of the limits)@ at time @t@.
limitNonCommutation :: Double -> Double -> Double -> (Double, Double)
limitNonCommutation kappa m t = (head coupledLimit, head freeComposite)
  where
    steps = 20000
    h     = t / fromIntegral steps
    y0    = [0, 0, 1, 0]      -- q1 = 0, p1 = 0, q2 = 1, p2 = 0
    coupledLimit  = integrate (vectorField (Params m 0 m 0 kappa kappa)) h steps y0
    freeComposite = integrate (vectorField (Params m 0 m 0 0     0    )) h steps y0

-- | EL-P4.  Gap between the oscillator trajectory and the free trajectory at
-- a chosen time; used both on a bounded interval and at @t = 2 pi / w@.
oscillatorFreeLimitGap :: Double -> Double -> Double -> Double -> Double
oscillatorFreeLimitGap w q0 v0 t = abs (osc - free)
  where
    osc  = q0 * cos (w * t) + (v0 / w) * sin (w * t)
    free = q0 + v0 * t

-- | Relativistic kinetic energy, written in the algebraically equivalent but
-- numerically stable form @p^2 c^2 / (sqrt(m^2 c^4 + p^2 c^2) + m c^2)@ to
-- avoid catastrophic cancellation at large @c@.
kineticRelativistic :: Double -> Double -> Double -> Double
kineticRelativistic m c p = (p * p * c * c) / (sqrt (m*m*c*c*c*c + p*p*c*c) + m*c*c)

kineticNewtonian :: Double -> Double -> Double
kineticNewtonian m p = p * p / (2 * m)

-- | Supremum gap over a momentum grid (EL-P3).
newtonianGapOn :: Double -> Double -> [Double] -> Double
newtonianGapOn m c ps =
  maximum (0 : map (\p -> abs (kineticRelativistic m c p - kineticNewtonian m p)) ps)

-- ---------------------------------------------------------------------------
-- 8. Finite-data underdetermination  (EL-N2)
-- ---------------------------------------------------------------------------

-- | For sample times @ts@ and a base trajectory @q@, the perturbed
-- trajectory @q + lambda * prod_k (t - t_k)@ agrees with @q@ at every sample
-- time and differs elsewhere.  Returns @(max residual on samples, residual
-- at the off-sample probe)@.
sampleAmbiguity :: [Double] -> (Double -> Double) -> Double -> Double -> (Double, Double)
sampleAmbiguity ts q lam probe = (onSamples, offSample)
  where
    bump t   = product [t - tk | tk <- ts]
    qlam t   = q t + lam * bump t
    onSamples = maximum (0 : map (\t -> abs (qlam t - q t)) ts)
    offSample = abs (qlam probe - q probe)

-- ---------------------------------------------------------------------------
-- 9. Report
-- ---------------------------------------------------------------------------

-- | Tolerance for quantities that should agree to integrator/round-off level.
tolStrict :: Double
tolStrict = 1e-9

-- | Tolerance below which a coupling matrix counts as vanishing.
tolLoose :: Double
tolLoose = 1e-12

check :: String -> Bool -> IO Bool
check name ok = do
  printf "  [%s] %s\n" (if ok then "PASS" else "FAIL" :: String) name
  return ok

section :: String -> IO ()
section s = putStrLn ("\n" ++ s ++ "\n" ++ replicate (length s) '-')

main :: IO ()
main = do
  putStrLn "PRINCIPIA PHYSICA -- Core.hs executable witnesses"
  putStrLn "Every result below is a decision procedure or a numerical witness."
  putStrLn "None of them is a proof."
  printf "Declared tolerances: strict = %.1e, loose = %.1e\n" tolStrict tolLoose

  section "0. Epistemic registry"
  r1 <- check "every declared dependency names a declared claim"
              (registryWellFormed registry)
  r2 <- check "no proved-label claim has an empty dependency list"
              (registryNoFreeProofs registry)
  putStrLn ("  labels in use: " ++
            intercalate ", " (map (show . claimLabel) registry))

  section "1. Typed composition (CS-D1, CS-D3, CS-P1, CS-D5)"
  let sysA = Sys (\o x -> o * x)                 :: Sys Double Double Double
      sysB = Sys (\o y -> o * y)                 :: Sys Double Double Double
      comp = parSys sysA sysB
      states = [(u, v) | u <- [0, 1, 2.5], v <- [-1, 0, 3]]
  r3 <- check "left projection satisfies the CS-D3 coherence equation"
              (coherentOn comp sysA projL states [1, 2, 0.5])
  r4 <- check "right projection satisfies the CS-D3 coherence equation"
              (coherentOn comp sysB projR states [1, 2, 0.5])
  r5 <- check "identity is a unit for typed composition on the sampled states"
              (map (procFwd (compProc (idProc :: Proc Double Double Double Double)
                                      (idProc :: Proc Double Double Double Double)))
                   [0, 1, 2] == [0, 1, 2 :: Double])

  section "2. Reciprocity trichotomy (HR-N1, S-N1)"
  let c12a = [[1, 2], [3, 4]] :: Matrix
      c21a = transposeM c12a
      c21b = [[1, 2], [3, 4]] :: Matrix
      z    = zeroM 2 2
  printf "  defect ||C21^T - C12||_F, reciprocal case   = %.3e\n"
         (frobenius (reciprocityDefect c12a c21a))
  printf "  defect ||C21^T - C12||_F, non-reciprocal    = %.3e\n"
         (frobenius (reciprocityDefect c12a c21b))
  r6 <- check "C21 = C12^T classified ReciprocalCoupled"
              (classifyCoupling tolLoose c12a c21a == ReciprocalCoupled)
  r7 <- check "C21 /= C12^T classified NonReciprocal"
              (classifyCoupling tolLoose c12a c21b == NonReciprocal)
  r8 <- check "zero couplings classified Decoupled"
              (classifyCoupling tolLoose z z == Decoupled)
  r9 <- check "HR-N2 scalar: unidirectional coupling admits no split-respecting form"
              (splitInvariantScalar tolLoose 1.0 0.0 == Nothing)
  r10 <- check "HR-N2 scalar: bidirectional coupling admits witness (a1,a2)=(c21,c12)"
               (splitInvariantScalar tolLoose 2.0 5.0 == Just (5.0, 2.0))
  r11 <- check "HR-P3: divergence vanishes for every coupling (volume preserved)"
               (divergenceLinear (Params 1 1 1 1 7 (-3)) == 0)

  section "3. Additive dynamics factorize; coupled dynamics do not (CS-T1, CS-C1)"
  let y0        = [1, 0, 0, 1] :: [Double]
      decoupled = Params 1 1 2 3 0 0
      coupled   = Params 1 1 2 3 0.5 0.5
      resD = factorizationResidual decoupled 1e-3 1000 y0
      resC = factorizationResidual coupled   1e-3 1000 y0
  printf "  residual, decoupled composite at t=1 : %.3e\n" resD
  printf "  residual, reciprocally coupled at t=1: %.3e\n" resC
  r12 <- check "decoupled composite flow factorizes to integrator accuracy" (resD <= tolStrict)
  r13 <- check "reciprocally coupled composite flow does NOT factorize"     (resC >  1e-3)

  section "4. Isomorphism does not fix protocol distinctions (HR-N3, S-N2)"
  let m1 = 1.0; m2 = 4.0; w0 = 1.0; t0 = 1.0
      readM1 = portReading m1 w0 0 1 t0
      readM2 = portReading m2 w0 0 1 t0
      hres   = transportedHamiltonianResidual m1 m2 w0 0.7 1.3
  printf "  alpha = sqrt(m/m')                    = %.6f\n" (transportAlpha m1 m2)
  printf "  |H_m(q,p) - H_m'(F(q,p))|             = %.3e\n" (abs hres)
  printf "  port reading q(1), m=1                = %.6f\n" readM1
  printf "  port reading q(1), m=4                = %.6f\n" readM2
  r14 <- check "closed systems are isomorphic: transported Hamiltonians agree"
               (abs hres <= tolStrict)
  r15 <- check "yet the untransported port reading separates the two masses"
               (not (obsEquivExact [t0] (portReading m1 w0 0 1) (portReading m2 w0 0 1)))

  section "5. Limits need not commute with composition (S-N3)"
  let (qCoupledLimit, qFreeComposite) = limitNonCommutation 1.0 1.0 1.0
  printf "  q1(1), limit of the composite (kappa=1) = %.6f\n" qCoupledLimit
  printf "  q1(1), composite of the limits         = %.6f\n" qFreeComposite
  r16 <- check "the two orders of (limit, compose) give different q1(1)"
               (abs (qCoupledLimit - qFreeComposite) > 1e-3)

  section "6. Bounded-domain limits only (EL-P3, EL-P4)"
  let psBounded = [0, 0.1 .. 5]
  printf "  sup|T_c - T_N| on |p|<=5,  c=10        = %.3e\n" (newtonianGapOn 1 10   psBounded)
  printf "  sup|T_c - T_N| on |p|<=5,  c=1000      = %.3e\n" (newtonianGapOn 1 1000 psBounded)
  printf "  |T_c - T_N| at p = m c,    c=1000      = %.3e\n" (newtonianGapOn 1 1000 [1000])
  r17 <- check "Newtonian gap shrinks on a bounded momentum window as c grows"
               (newtonianGapOn 1 1000 psBounded < newtonianGapOn 1 10 psBounded)
  r18 <- check "Newtonian gap grows without bound along p = m c"
               (newtonianGapOn 1 1000 [1000] > newtonianGapOn 1 10 [10])
  printf "  oscillator gap at t=1,       w=1e-3    = %.3e\n" (oscillatorFreeLimitGap 1e-3 1 1 1)
  printf "  oscillator gap at t=2 pi / w, w=1e-3   = %.3e\n"
         (oscillatorFreeLimitGap 1e-3 1 1 (2 * pi / 1e-3))
  r19 <- check "oscillator -> free on bounded time, but not uniformly in time"
               (oscillatorFreeLimitGap 1e-3 1 1 1 < 1e-4 &&
                oscillatorFreeLimitGap 1e-3 1 1 (2 * pi / 1e-3) > 1e3)

  section "7. Protocol relations and finite data (EL-P1 counterexample, EL-N2)"
  let (ab, bc, ac) = transitivityWitness 0.1
  printf "  eps-equivalence verdicts (A~B, B~C, A~C) = (%s, %s, %s)\n"
         (show ab) (show bc) (show ac)
  r20 <- check "approximate equivalence is not transitive"
               (ab && bc && not ac)
  let (onS, offS) = sampleAmbiguity [0, 1, 2, 3] (\t -> t * t) 1.0 0.5
  printf "  max residual at the 4 sample times      = %.3e\n" onS
  printf "  residual at off-sample probe t = 0.5    = %.3e\n" offS
  r21 <- check "distinct trajectories agree exactly on the finite sample"
               (onS <= tolStrict && offS > 1e-3)

  section "Summary"
  let results = [ r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
                , r12, r13, r14, r15, r16, r17, r18, r19, r20, r21 ]
      passed  = length (filter id results)
      total   = length results
  printf "  %d / %d witnesses passed\n" passed total
  putStrLn "  Reminder: passing witnesses do not establish any universal claim."
  if passed == total then exitSuccess else exitFailure
