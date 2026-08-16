-- |
-- Module      : Main
-- Description : Executable companions to the PRINCIPIA PHYSICA synthesis paper.
--
-- Accompanies "Empirical Realization of Compositional Structure: A Synthesis
-- of the PRINCIPIA PHYSICA Topic Series" (papers/drafts/synthesis.tex) and the
-- Lean development (formal/drafts/Proofs.lean).
--
-- Dependencies: @base@ only.  Written to the Haskell 2010 report plus
-- @ScopedTypeVariables@ so that it builds under old and current GHC alike.
--
-- EPISTEMIC STATUS.  This program computes.  It does not measure.  Every
-- numerical check below is a check that a /mathematical/ construction behaves
-- as the paper proves it behaves; none of them is evidence that any model is
-- physically realized.  Where a quantity would in practice come from an
-- instrument, it is supplied here as a literal and labelled @synthetic@.
--
-- Running @main@ executes every check and exits non-zero if any fails, so the
-- file doubles as a regression test for the paper's computational claims.
--
-- Section map (numbers refer to synthesis.tex):
--   1. Numerical helpers
--   2. Interface theories as a typed process DSL          (Def. 2.1)
--   3. A model: the stochastic-matrix functor             (Thm. 2.4, Ex. 2.7)
--   4. The kernel construction: bump perturbations        (Thm. 3.2, Cor. 3.4)
--   5. Gauge freedom and reconstruction up to a constant  (Prop. 4.4)
--   6. Hamiltonian dynamics and finite-sample identification (Cor. 3.5)
--   7. Compatibility regions and monotonicity             (Prop. 2.8)
--   8. Scope: extrapolation and composition bounds        (Lem. 7.1, Prop. 7.2)
--   9. Harness

{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import           Control.Monad (forM_, unless)
import           Data.List     (transpose)
import           System.Exit   (exitFailure)
import           Text.Printf   (printf)

-- ---------------------------------------------------------------------------
-- 1.  Numerical helpers
-- ---------------------------------------------------------------------------

-- | Tolerance used for exact-arithmetic identities that are exact in theory
-- and only floating-point-exact in practice.
eps :: Double
eps = 1.0e-9

close :: Double -> Double -> Double -> Bool
close t a b = abs (a - b) <= t

-- | Row-major real matrices.  Composition is matrix product; the categorical
-- convention is @matMul g f@ for \"first f, then g\".
type Mat = [[Double]]

matRows :: Mat -> Int
matRows = length

matCols :: Mat -> Int
matCols m = case m of
  []      -> 0
  (r : _) -> length r

matId :: Int -> Mat
matId n = [ [ if i == j then 1 else 0 | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]

matMul :: Mat -> Mat -> Mat
matMul a b = [ [ sum (zipWith (*) row col) | col <- transpose b ] | row <- a ]

-- | Kronecker product; the interpretation of parallel composition.
kron :: Mat -> Mat -> Mat
kron a b = [ concat [ map (x *) rb | x <- ra ] | ra <- a, rb <- b ]

matClose :: Double -> Mat -> Mat -> Bool
matClose t a b =
  length a == length b
    && and (zipWith (\r s -> length r == length s && and (zipWith (close t) r s)) a b)

-- | Column-stochasticity: every column is a probability vector.  This is the
-- property the probabilistic-interpretation assumption of the compositional
-- paper requires, and it is preserved by both forms of composition.
isColStochastic :: Double -> Mat -> Bool
isColStochastic t m =
  all (all (>= negate t)) m
    && all (\c -> close t (sum c) 1) (transpose m)

-- ---------------------------------------------------------------------------
-- 2.  Interface theories as a typed process DSL
-- ---------------------------------------------------------------------------

-- | Interface types.  @TPair@ is the monoidal product; @TUnit@ its unit.
data Ty = TUnit | TBit | TPair Ty Ty
  deriving (Eq, Show)

dim :: Ty -> Int
dim TUnit       = 1
dim TBit        = 2
dim (TPair a b) = dim a * dim b

-- | Process expressions.  @PGen@ carries the matrix a model assigns to a
-- generator; the syntax is thereby a free process theory over a signature.
data Proc
  = PId Ty
  | PComp Proc Proc          -- ^ @PComp g f@ is \"f then g\".
  | PTensor Proc Proc
  | PSwap Ty Ty
  | PGen String Ty Ty Mat
  deriving (Show)

-- | Type checking is the admissibility test at the syntactic level: it decides
-- whether an expression denotes a process at all.  It says nothing about
-- whether the process can be run in a laboratory.
typeOf :: Proc -> Either String (Ty, Ty)
typeOf (PId t) = Right (t, t)
typeOf (PComp g f) = do
  (fx, fy) <- typeOf f
  (gy, gz) <- typeOf g
  if fy == gy
    then Right (fx, gz)
    else Left ("sequential mismatch: " ++ show fy ++ " /= " ++ show gy)
typeOf (PTensor p q) = do
  (a, b) <- typeOf p
  (c, d) <- typeOf q
  Right (TPair a c, TPair b d)
typeOf (PSwap a b) = Right (TPair a b, TPair b a)
typeOf (PGen nm a b m) =
  if matRows m == dim b && matCols m == dim a
    then Right (a, b)
    else Left ("generator " ++ nm ++ " has wrong shape")

-- | The permutation exchanging the two factors of a tensor product.
swapMat :: Int -> Int -> Mat
swapMat da db =
  [ [ if r == j * da + i then 1 else 0 | i <- [0 .. da - 1], j <- [0 .. db - 1] ]
  | r <- [0 .. da * db - 1]
  ]

-- ---------------------------------------------------------------------------
-- 3.  A model: the stochastic-matrix functor
-- ---------------------------------------------------------------------------

-- | The model of claim C1, concretely: a strong symmetric monoidal functor into
-- finite stochastic maps.  @interp@ is total on well-typed expressions.
interp :: Proc -> Mat
interp (PId t)        = matId (dim t)
interp (PComp g f)    = matMul (interp g) (interp f)
interp (PTensor p q)  = kron (interp p) (interp q)
interp (PSwap a b)    = swapMat (dim a) (dim b)
interp (PGen _ _ _ m) = m

-- Synthetic generators.  These numbers are stipulated, not measured.
noisyNot :: Proc
noisyNot = PGen "noisyNot" TBit TBit [[0.1, 0.9], [0.9, 0.1]]

decay :: Proc
decay = PGen "decay" TBit TBit [[1.0, 0.3], [0.0, 0.7]]

mix :: Proc
mix = PGen "mix" TBit TBit [[0.5, 0.5], [0.5, 0.5]]

-- | Functoriality check 1: associativity of sequential composition is preserved.
checkAssoc :: Bool
checkAssoc =
  matClose eps
    (interp (PComp (PComp decay noisyNot) mix))
    (interp (PComp decay (PComp noisyNot mix)))

-- | Functoriality check 2: the interchange law
-- @(g . f) (x) (g' . f') = (g (x) g') . (f (x) f')@ is preserved.  This is the
-- single equation that makes sequential and parallel composition cohere, and
-- Thm. 2.4 says a monoidal functor must respect it.
checkInterchange :: Bool
checkInterchange =
  matClose eps
    (interp (PTensor (PComp decay noisyNot) (PComp mix decay)))
    (interp (PComp (PTensor decay mix) (PTensor noisyNot decay)))

-- | Functoriality check 3: naturality of the symmetry,
-- @swap . (f (x) g) = (g (x) f) . swap@.
checkSwapNatural :: Bool
checkSwapNatural =
  matClose eps
    (interp (PComp (PSwap TBit TBit) (PTensor noisyNot decay)))
    (interp (PComp (PTensor decay noisyNot) (PSwap TBit TBit)))

-- | The probabilistic interpretation is preserved by composition.
checkStochasticClosure :: Bool
checkStochasticClosure =
  all (isColStochastic eps . interp)
    [ noisyNot
    , decay
    , mix
    , PComp decay noisyNot
    , PTensor noisyNot decay
    , PComp (PSwap TBit TBit) (PTensor noisyNot decay)
    ]

-- | Every expression used above is well typed.
checkTyping :: Bool
checkTyping =
  all wellTyped
    [ PComp (PComp decay noisyNot) mix
    , PTensor (PComp decay noisyNot) (PComp mix decay)
    , PComp (PSwap TBit TBit) (PTensor noisyNot decay)
    ]
    && not (wellTyped (PComp noisyNot (PId TUnit)))
  where
    wellTyped p = case typeOf p of
      Right _ -> True
      Left _  -> False

-- | Admissibility is not realization, in the smallest possible instance.  Two
-- models of the same one-generator theory agree on the identity-context
-- observation and differ on a one-use experiment; the syntax cannot choose.
checkAdmissibleNotRealized :: (Bool, Double, Double)
checkAdmissibleNotRealized = (differ, pF, pG)
  where
    stateIn  = [[1.0], [0.0]]                 -- prepare the first basis outcome
    effect   = [[1.0, 0.0]]                   -- ask for the first basis outcome
    modelF   = interp noisyNot
    modelG   = interp (PComp noisyNot noisyNot)
    scalar m = case matMul effect (matMul m stateIn) of
      ((x : _) : _) -> x
      _             -> 0
    pF       = scalar modelF
    pG       = scalar modelG
    differ   = abs (pF - pG) > 1.0e-3

-- ---------------------------------------------------------------------------
-- 4.  The kernel construction: bump perturbations
-- ---------------------------------------------------------------------------

-- | The standard smooth bump: positive on @(-1,1)@, identically zero outside,
-- and flat to infinite order at the boundary.  This is the witness used in the
-- proof of the kernel theorem and of its Hamiltonian corollary.
bump :: Double -> Double
bump x
  | abs x < 1 = exp (1 / (x * x - 1))
  | otherwise = 0

-- | A bump of height scale @lam@ centred at @c@ with radius @r@.
bumpAt :: Double -> Double -> Double -> Double -> Double
bumpAt c r lam x = lam * bump ((x - c) / r)

-- | The tested set.  Synthetic: these are the inputs we stipulate were probed.
testedInputs :: [Double]
testedInputs = [0, 1, 2, 3, 4, 5]

baseModel :: Double -> Double
baseModel = sin

-- | A member of the kernel of the restriction operator: it vanishes on every
-- tested input because its support @(6,8)@ misses all of them.
kernelPerturbation :: Double -> Double
kernelPerturbation = bumpAt 7 1 1

perturbedModel :: Double -> Double
perturbedModel x = baseModel x + kernelPerturbation x

-- | Records agree exactly; the models differ off the tested set.  Reported as
-- (records agree, max on-test discrepancy, off-test discrepancy at 7).
checkKernelUnderdetermination :: (Bool, Double, Double)
checkKernelUnderdetermination = (agree && separated, onTest, offTest)
  where
    onTest    = maximum [ abs (perturbedModel x - baseModel x) | x <- testedInputs ]
    offTest   = abs (perturbedModel 7 - baseModel 7)
    agree     = onTest <= eps
    separated = offTest > 0.1

-- | The Hamiltonian corollary needs more than agreement of values: the
-- perturbation must have vanishing /derivative/ at each sample, so that the
-- generated vector fields agree there too.  A bump supported off the sample set
-- satisfies this automatically.  Checked by central differences.
checkKernelDerivatives :: (Bool, Double)
checkKernelDerivatives = (worst <= 1.0e-9, worst)
  where
    h = 1.0e-5
    d f x = (f (x + h) - f (x - h)) / (2 * h)
    worst = maximum [ abs (d perturbedModel x - d baseModel x) | x <- testedInputs ]

-- | Restricting the model class restores identification.  A polynomial of
-- degree at most @d@ is fixed by @d+1@ values, so no nonzero kernel element
-- survives inside that class: identification comes from the degree bound, not
-- from the data.  Checked by Lagrange interpolation and reconstruction.
checkPolynomialIdentification :: (Bool, Double)
checkPolynomialIdentification = (worst <= 1.0e-8, worst)
  where
    truth x = 2 * x * x * x - x + 3
    nodes   = [-2, -1, 0, 1]
    ys      = map truth nodes
    lagrange x =
      sum
        [ y * product [ (x - xj) / (xi - xj) | xj <- nodes, xj /= xi ]
        | (xi, y) <- zip nodes ys
        ]
    worst = maximum [ abs (lagrange x - truth x) | x <- [-3, -2.5 .. 3] ]

-- ---------------------------------------------------------------------------
-- 5.  Gauge freedom and reconstruction up to a constant
-- ---------------------------------------------------------------------------

-- | Forward difference: the discrete analogue of @H |-> dH@.
diffSeq :: [Double] -> [Double]
diffSeq xs = zipWith (-) (drop 1 xs) xs

-- | Reconstruct a sequence from its differences and a chosen base point.  The
-- base point is the gauge choice; nothing in the data selects it.
integrateSeq :: Double -> [Double] -> [Double]
integrateSeq = scanl (+)

sampleH :: [Double]
sampleH = [ 0.5 * (fromIntegral n) ** 2 - 3 * fromIntegral (n :: Int) | n <- [0 .. 12] ]

-- | Additive constants are invisible, and reconstruction recovers the sequence
-- exactly once a base point is fixed.  Reported as
-- (shift invisible, reconstruction exact, worst reconstruction error).
checkGauge :: (Bool, Bool, Double)
checkGauge = (invisible, exact, worst)
  where
    shifted   = map (+ 17.25) sampleH
    invisible = and (zipWith (close eps) (diffSeq shifted) (diffSeq sampleH))
    rebuilt   = integrateSeq base (diffSeq sampleH)
    base      = case sampleH of
      x : _ -> x
      []    -> 0
    worst     = maximum (zipWith (\a b -> abs (a - b)) rebuilt sampleH)
    exact     = worst <= eps

-- | With the /wrong/ base point the reconstruction is wrong by exactly the
-- gauge constant, everywhere and by the same amount.  This is what
-- "identifiable up to an additive constant" means operationally.
checkGaugeOrbit :: (Bool, Double)
checkGaugeOrbit = (uniform, spread)
  where
    c        = 4.75
    rebuilt  = integrateSeq (base + c) (diffSeq sampleH)
    base     = case sampleH of
      x : _ -> x
      []    -> 0
    errs     = zipWith (-) rebuilt sampleH
    spread   = maximum errs - minimum errs
    firstErr = case errs of
      x : _ -> x
      []    -> 0
    uniform  = spread <= eps && close eps firstErr c

-- ---------------------------------------------------------------------------
-- 6.  Hamiltonian dynamics and finite-sample identification
-- ---------------------------------------------------------------------------

-- | @H(q,p) = (a p^2 + b q^2) / 2@.  Synthetic parameters.
hamA, hamB :: Double
hamA = 1.0
hamB = 4.0

energy :: (Double, Double) -> Double
energy (q, p) = 0.5 * (hamA * p * p + hamB * q * q)

-- | One Stoermer-Verlet (leapfrog) step.  Symplectic, second order; the
-- relevant point for the paper is that it conserves a /modified/ energy
-- exactly and the true energy to O(dt^2), so \"energy is conserved\" is a
-- statement about the model, discretization and all.
verletStep :: Double -> (Double, Double) -> (Double, Double)
verletStep dt (q, p) =
  let qh = q + 0.5 * dt * hamA * p
      p' = p - dt * hamB * qh
      q' = qh + 0.5 * dt * hamA * p'
  in (q', p')

trajectory :: Double -> Int -> (Double, Double) -> [(Double, Double)]
trajectory dt n z0 = take (n + 1) (iterate (verletStep dt) z0)

-- | Relative energy drift over a long run.  Reported, then compared against a
-- stated threshold; the threshold is a modelling choice, not a law.
checkEnergyDrift :: (Bool, Double)
checkEnergyDrift = (drift <= 2.0e-4, drift)
  where
    dt     = 0.005
    z0     = (1.0, 0.0)
    es     = map energy (trajectory dt 40000 z0)
    e0     = energy z0
    drift  = maximum (map (\e -> abs (e - e0) / e0) es)

-- | Exact-derivative identification in the two-parameter class
-- @H = (a p^2 + b q^2)/2@.  The design is the 2x2 matrix @[[p,0],[0,-q]]@;
-- it is invertible exactly when both @p@ and @q@ are nonzero at the sample.
identifyAB :: (Double, Double) -> Maybe (Double, Double)
identifyAB (q, p)
  | abs p < 1.0e-12 || abs q < 1.0e-12 = Nothing
  | otherwise = Just (qdot / p, negate pdot / q)
  where
    qdot = hamA * p            -- dq/dt =  dH/dp
    pdot = negate (hamB * q)   -- dp/dt = -dH/dq

-- | A generic sample identifies both parameters; a sample confined to @q = 0@
-- carries no information about @b@ and the procedure correctly refuses.
checkIdentification :: (Bool, String)
checkIdentification =
  case (identifyAB (0.7, 1.3), identifyAB (0.0, 1.3)) of
    (Just (a, b), Nothing) ->
      ( close 1.0e-12 a hamA && close 1.0e-12 b hamB
      , printf "recovered a=%.6f b=%.6f; degenerate design at q=0 refused" a b
      )
    (Just _, Just _)  -> (False, "degenerate design at q=0 was not detected")
    (Nothing, _)      -> (False, "generic sample failed to identify")

-- | The clock ambiguity: reparametrising time by a positive factor leaves the
-- unparameterised orbit unchanged while changing every rate.  Checked by
-- confirming that the scaled field traces the same energy level set.
checkClockAmbiguity :: (Bool, Double)
checkClockAmbiguity = (sameOrbit, worst)
  where
    lam    = 2.5
    z0     = (1.0, 0.0)
    e0     = energy z0
    -- Scaling the vector field by lam is the same as scaling dt by lam.
    zs     = trajectory (0.002 * lam) 2000 z0
    worst  = maximum [ abs (energy z - e0) / e0 | z <- zs ]
    sameOrbit = worst <= 1.0e-3

-- ---------------------------------------------------------------------------
-- 7.  Compatibility regions and monotonicity
-- ---------------------------------------------------------------------------

-- | Synthetic record: tested inputs paired with stipulated observed values and
-- a stated tolerance.  Nothing here was measured.
syntheticRecord :: [(Double, Double)]
syntheticRecord = [ (x, sin x + 0.01 * cos (3 * x)) | x <- testedInputs ]

compatible :: [(Double, Double)] -> Double -> (Double -> Double) -> Bool
compatible obs tolr m = all (\(x, y) -> abs (m x - y) <= tolr) obs

-- | Monotonicity in the tolerance and in the tested set, checked over a grid.
-- Both are one-line consequences of transitivity of @<=@; the check exists to
-- keep the paper's Prop. 2.8 executable.
checkCompatibilityMonotone :: (Bool, Bool)
checkCompatibilityMonotone = (tolMono, testMono)
  where
    tols    = [0.005, 0.01, 0.02, 0.05, 0.1]
    models  = [baseModel, perturbedModel, \x -> sin x + 0.03]
    tolMono = and
      [ not (compatible syntheticRecord t1 m) || compatible syntheticRecord t2 m
      | m <- models, t1 <- tols, t2 <- tols, t1 <= t2
      ]
    subsets = [ take k syntheticRecord | k <- [0 .. length syntheticRecord] ]
    testMono = and
      [ not (compatible syntheticRecord t m) || compatible s t m
      | m <- models, t <- tols, s <- subsets
      ]

-- | The compatibility region is not a singleton: base and perturbed models are
-- both compatible with the same record at the same tolerance, yet differ off
-- the tested set.  This is the executable form of the kernel theorem.
checkCompatibilityNotSingleton :: (Bool, Double)
checkCompatibilityNotSingleton = (both, gap)
  where
    t    = 0.02
    both = compatible syntheticRecord t baseModel
             && compatible syntheticRecord t perturbedModel
    gap  = abs (perturbedModel 7 - baseModel 7)

-- ---------------------------------------------------------------------------
-- 8.  Scope: extrapolation and composition bounds
-- ---------------------------------------------------------------------------

-- | The bound of the empirical-limits paper: on a set covered to radius @r@ by
-- tested points, with both model and target @L@-Lipschitz and tested error at
-- most @e@, the error anywhere on the set is at most @e + 2 L r@.
scopeBound :: Double -> Double -> Double -> Double
scopeBound e l r = e + 2 * l * r

-- | Checked against a concrete pair on a covered interval.
checkScopeBound :: (Bool, Double, Double)
checkScopeBound = (actual <= bound + eps, actual, bound)
  where
    l       = 1.0                            -- both maps are 1-Lipschitz
    r       = 0.05                           -- covering radius of the grid
    grid    = [0, 0.1 .. 1.0]
    target  = sin
    model x = sin x + 0.004
    e       = maximum [ abs (model x - target x) | x <- grid ]
    bound   = scopeBound e l r
    actual  = maximum [ abs (model x - target x) | x <- [0, 0.001 .. 1.0] ]

-- | The composition bound of Lem. 7.1: with an @L@-Lipschitz outer map, errors
-- compose as @L * e1 + e2@.  Checked on a case where the bound is attained
-- exactly, so a wrong constant would show up immediately.
checkCompositionBound :: (Bool, Double, Double)
checkCompositionBound = (actual <= bound + 1.0e-12, actual, bound)
  where
    l      = 2.0
    e1     = 0.01
    e2     = 0.02
    f1 x   = x * x
    g1 x   = x * x + e1
    f2 y   = l * y
    g2 y   = l * y + e2
    bound  = l * e1 + e2
    actual = maximum [ abs (f2 (f1 x) - g2 (g1 x)) | x <- [0, 0.01 .. 1.0] ]

-- | The @n@-fold version: along a chain the tolerances accumulate as
-- @sum_i (prod_{j>i} L_j) e_i@.  Checked for a three-stage chain.
checkChainBound :: (Bool, Double, Double)
checkChainBound = (actual <= bound + 1.0e-12, actual, bound)
  where
    ls     = [1.5, 2.0, 0.5] :: [Double]     -- L1 (unused), L2, L3
    es     = [0.01, 0.02, 0.005] :: [Double]
    bound  = sum [ e * product (drop (i + 1) ls) | (i, e) <- zip [0 ..] es ]
    stage k x = (ls !! k) * x
    stageH k x = (ls !! k) * x + (es !! k)
    exact  = stage 2 . stage 1 . stage 0
    approx = stageH 2 . stageH 1 . stageH 0
    actual = maximum [ abs (exact x - approx x) | x <- [0, 0.01 .. 1.0] ]

-- | Componentwise data does not determine the composite.  Two joint models
-- share every single-component marginal and disagree on the joint event that
-- the two outputs coincide.  This is why the composition bound above is a
-- statement about deterministic scope, not about joint statistics: closing
-- that gap needs the empirical assumption of compositional closure.
checkCompositionCounterexample :: (Bool, Double, Double)
checkCompositionCounterexample = (marginalsAgree && jointsDiffer, pInd, pCorr)
  where
    independent = [0.25, 0.25, 0.25, 0.25] :: [Double]   -- 00 01 10 11
    correlated  = [0.5, 0.0, 0.0, 0.5] :: [Double]
    marg1 (a : b : _c : _d : _) = a + b
    marg1 _ = 0
    marg2 (a : _b : c : _d : _) = a + c
    marg2 _ = 0
    marginalsAgree =
      close eps (marg1 independent) (marg1 correlated)
        && close eps (marg2 independent) (marg2 correlated)
    coincide (a : _b : _c : d : _) = a + d
    coincide _ = 0
    pInd  = coincide independent
    pCorr = coincide correlated
    jointsDiffer = abs (pInd - pCorr) > 0.1

-- ---------------------------------------------------------------------------
-- 9.  Harness
-- ---------------------------------------------------------------------------

data Check = Check
  { checkLabel  :: String
  , checkPassed :: Bool
  , checkNote   :: String
  }

allChecks :: [Check]
allChecks =
  [ Check "2. well-typed expressions accepted, ill-typed rejected"
      checkTyping ""
  , Check "3. functor preserves associativity"
      checkAssoc ""
  , Check "3. functor preserves the interchange law"
      checkInterchange ""
  , Check "3. functor preserves naturality of the symmetry"
      checkSwapNatural ""
  , Check "3. probabilistic interpretation closed under composition"
      checkStochasticClosure ""
  , Check "3. two admissible models give different predictions"
      admOk (printf "p_F = %.4f, p_G = %.4f" admPF admPG)
  , Check "4. kernel perturbation: records agree, models differ"
      kerOk (printf "on-test max = %.2e, off-test gap = %.4f" kerOn kerOff)
  , Check "4. kernel perturbation also kills first derivatives"
      derOk (printf "max derivative discrepancy on tests = %.2e" derWorst)
  , Check "4. degree bound restores identification"
      polyOk (printf "max reconstruction error = %.2e" polyWorst)
  , Check "5. additive gauge invisible; reconstruction exact"
      (gInv && gExact) (printf "max reconstruction error = %.2e" gWorst)
  , Check "5. wrong base point shifts the whole orbit uniformly"
      orbOk (printf "spread of residuals = %.2e" orbSpread)
  , Check "6. symplectic integrator: energy drift bounded"
      eneOk (printf "max relative drift over 40000 steps = %.3e" eneDrift)
  , Check "6. generic sample identifies (a,b); q=0 design refused"
      idOk idNote
  , Check "6. time reparametrisation preserves the orbit"
      clkOk (printf "max relative energy deviation = %.2e" clkWorst)
  , Check "7. compatibility monotone in tolerance"
      cmTol ""
  , Check "7. compatibility monotone in tested set"
      cmTest ""
  , Check "7. compatibility region is not a singleton"
      cnsOk (printf "off-test gap between compatible models = %.4f" cnsGap)
  , Check "8. scope bound e + 2Lr holds off the tested grid"
      scOk (printf "actual = %.5f <= bound = %.5f" scAct scBnd)
  , Check "8. composition bound L*e1 + e2 holds and is attained"
      cbOk (printf "actual = %.5f <= bound = %.5f" cbAct cbBnd)
  , Check "8. three-stage chain bound holds"
      chOk (printf "actual = %.5f <= bound = %.5f" chAct chBnd)
  , Check "8. equal marginals, different joint: composition needs closure"
      ccOk (printf "P(agree) independent = %.2f, correlated = %.2f" ccInd ccCorr)
  ]
  where
    (admOk, admPF, admPG)     = checkAdmissibleNotRealized
    (kerOk, kerOn, kerOff)    = checkKernelUnderdetermination
    (derOk, derWorst)         = checkKernelDerivatives
    (polyOk, polyWorst)       = checkPolynomialIdentification
    (gInv, gExact, gWorst)    = checkGauge
    (orbOk, orbSpread)        = checkGaugeOrbit
    (eneOk, eneDrift)         = checkEnergyDrift
    (idOk, idNote)            = checkIdentification
    (clkOk, clkWorst)         = checkClockAmbiguity
    (cmTol, cmTest)           = checkCompatibilityMonotone
    (cnsOk, cnsGap)           = checkCompatibilityNotSingleton
    (scOk, scAct, scBnd)      = checkScopeBound
    (cbOk, cbAct, cbBnd)      = checkCompositionBound
    (chOk, chAct, chBnd)      = checkChainBound
    (ccOk, ccInd, ccCorr)     = checkCompositionCounterexample

main :: IO ()
main = do
  putStrLn "PRINCIPIA PHYSICA -- synthesis companion checks"
  putStrLn "(mathematical checks only; no empirical claim is made or tested)"
  putStrLn (replicate 78 '-')
  forM_ allChecks $ \c -> do
    printf "%-4s %-60s\n" (if checkPassed c then "PASS" else "FAIL") (checkLabel c)
    unless (null (checkNote c)) $ printf "     %s\n" (checkNote c)
  putStrLn (replicate 78 '-')
  let failed = length (filter (not . checkPassed) allChecks)
      total  = length allChecks
  printf "%d/%d checks passed\n" (total - failed) total
  unless (failed == 0) exitFailure
