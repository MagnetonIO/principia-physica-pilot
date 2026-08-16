-- |
-- Module      : Main (file: formal/haskell/Core.hs)
-- Series      : PRINCIPIA PHYSICA -- formal appendix to
--               "Compositional Realization, Hamiltonian Reconstruction, and
--                Empirical Limits: a synthesis"
--
-- EPISTEMIC STATUS OF THIS FILE.
--
-- This is a /typing and an executable illustration/, not a proof.  Three
-- distinct things appear below and they are labelled at every definition:
--
--   [TYPE]   a rendering of a definition of the series as a Haskell type.
--            A type-checked rendering certifies arity and dependency, and
--            nothing else.  In particular it does not certify that any
--            theorem of the series holds.
--
--   [DEC]    a decision procedure that is /exact/ on the finite data it is
--            given (mixed-difference separability, cycle sums, observational
--            classes of a finite model class).  A True answer is a proof
--            about the sampled grid only, never about the smooth object.
--
--   [NUM]    a floating-point illustration (RK4 trajectories, total-variation
--            distances).  These carry discretisation and rounding error and
--            establish nothing.  They are included because the series makes
--            quantitative claims whose shape is worth exhibiting.
--
-- Machine-checked statements live in @formal/lean/Proofs.lean@; the
-- separability criterion and the cycle-sum obstruction implemented here are
-- the two decision procedures whose correctness is proved there.
--
-- Toolchain: GHC 9.14.1 (aarch64-apple-darwin), @base@ only.
--   Build and run:  ghc -Wall -Wextra -Werror Core.hs -o core && ./core
--   Requires base >= 4.20 (foldl' re-exported from Prelude).
-- Exit status is 0 iff every check reports PASS.

module Main (main) where

import Control.Monad (forM_, unless)
import Data.List (nub)
import System.Exit (exitFailure, exitSuccess)
import Text.Printf (printf)

-- ===================================================================
-- 1.  Typed systems and composition            (compositional-systems)
-- ===================================================================

-- | [TYPE] A typed deterministic system: an update map and a readout.
-- Surrogate of Definition "System and state" of the compositional-systems
-- paper with the symplectic structure deliberately absent, so that no
-- statement about Hamiltonian mechanics can be read off this type.
data Sys i s o = Sys
  { step    :: i -> s -> s
  , readout :: s -> o
  }

-- | [TYPE] Parallel (monoidal) product.  Mirrors @Definition (Composite
-- system)@: independent inputs, independent states, paired readout.
par :: Sys i1 s1 o1 -> Sys i2 s2 o2 -> Sys (i1, i2) (s1, s2) (o1, o2)
par a b = Sys
  { step    = \(i, j) (x, y) -> (step a i x, step b j y)
  , readout = \(x, y) -> (readout a x, readout b y)
  }

-- | [TYPE] Serial composition, synchronous convention: the second component
-- consumes the /updated/ output of the first.  A different timing convention
-- is a different theory; the choice is data, not a derived fact.
serial :: Sys i s o -> Sys o t p -> Sys i (s, t) p
serial a b = Sys
  { step    = \i (x, y) -> let x' = step a i x in (x', step b (readout a x') y)
  , readout = \(_, y) -> readout b y
  }

-- | [TYPE] Iterate along a finite input word.
runSys :: Sys i s o -> [i] -> s -> s
runSys a is x0 = foldl' (flip (step a)) x0 is

-- | [DEC] The product run factors.  Proved in Lean (@Principia.runPar@); here
-- it is only re-checked on the supplied sample.
runParFactors :: (Eq s1, Eq s2)
              => Sys i1 s1 o1 -> Sys i2 s2 o2
              -> [(i1, i2)] -> (s1, s2) -> Bool
runParFactors a b is (x, y) =
  runSys (par a b) is (x, y)
    == (runSys a (map fst is) x, runSys b (map snd is) y)

-- ===================================================================
-- 2.  Separability and interaction          (CS-N1, HR interaction)
-- ===================================================================

-- | [DEC] Exact separability test on a finite grid.  A coupling
-- @v :: a -> b -> Integer@ restricted to @as x bs@ is additively separable
-- iff every mixed second difference vanishes.  Correctness of this criterion
-- is the Lean theorem @Principia.separable_iff_noMixedDifference@.
--
-- Reading: in the smooth setting the corresponding statement is the
-- separation equivalence (a Hamiltonian vector field on a connected product
-- splits iff its generator is additively separable up to a constant).  A
-- True answer here does /not/ establish that smooth statement.
separableOn :: [a] -> [b] -> (a -> b -> Integer) -> Bool
separableOn as bs v =
  and [ v a b + v a' b' == v a b' + v a' b
      | a <- as, a' <- as, b <- bs, b' <- bs ]

-- | [DEC] The witness construction from the same proof: @f a = v a b0@ and
-- @g b = v a0 b - v a0 b0@.  Returns 'Nothing' exactly when the grid test
-- fails, so a 'Just' answer carries a checkable decomposition.
splitCoupling :: [a] -> [b] -> (a -> b -> Integer)
              -> Maybe (a -> Integer, b -> Integer)
splitCoupling [] _ _ = Nothing
splitCoupling _ [] _ = Nothing
splitCoupling as@(a0 : _) bs@(b0 : _) v
  | not (separableOn as bs v) = Nothing
  | otherwise = Just (\a -> v a b0, \b -> v a0 b - v a0 b0)

-- | [DEC] Interaction detector on a product state space: a system is
-- non-interacting when neither factor's update reads the other factor's
-- state.  Surrogate of @HR new-interaction-outside-tensor@; the Lean file
-- proves that every @par a b@ passes and exhibits a coupled system that
-- fails, so no product decomposition of it exists.
nonInteractingOn :: (Eq s1, Eq s2)
                 => [i] -> [s1] -> [s2] -> Sys i (s1, s2) o -> Bool
nonInteractingOn is xs ys s =
  and [ fst (step s i (x, y)) == fst (step s i (x, y'))
      | i <- is, x <- xs, y <- ys, y' <- ys ]
  &&
  and [ snd (step s i (x, y)) == snd (step s i (x', y))
      | i <- is, x <- xs, x' <- xs, y <- ys ]

-- ===================================================================
-- 3.  Discrete reconstruction and its period obstruction        (HR)
-- ===================================================================

-- | [DEC] Cycle sum of an @n@-periodic integer "one-form".  This single
-- integer plays the role of the de Rham class @[iota_X omega]@ in the
-- Hamiltonian-reconstruction paper.  The analogy is structural only: there
-- is no manifold and no symplectic form here.
cycleSum :: Int -> (Int -> Integer) -> Integer
cycleSum n alpha = sum [ alpha k | k <- [0 .. n - 1] ]

-- | [DEC] Global potential of a periodic form, or 'Nothing' when the period
-- obstructs it.  Necessity and sufficiency are both proved in Lean
-- (@cycle_sum_zero_of_potential@, @potential_of_cycle_sum_zero@).
--
-- The 'Nothing' branch is the discrete counterpart of the 2-torus
-- non-example: a form that is closed everywhere and has no global primitive.
potential :: Int -> (Int -> Integer) -> Maybe (Int -> Integer)
potential n alpha
  | n <= 0             = Nothing
  | cycleSum n alpha /= 0 = Nothing
  | otherwise          = Just (\k -> sum [ alpha j | j <- [0 .. k - 1] ])

-- | [DEC] Forward difference; a constant is invisible to it.  Discrete image
-- of @H@ and @H + c@ generating the same field, hence of the corollary that
-- the flow determines the generator only up to an additive constant.
diffSeq :: (Int -> Integer) -> Int -> Integer
diffSeq h k = h (k + 1) - h k

-- ===================================================================
-- 4.  The theory object and its interpretation                  (HR)
-- ===================================================================

-- | [TYPE] A point of a two-dimensional numerical phase space.  Finite
-- dimension is a stipulation of the series (Axiom: kinematic type); the
-- restriction to one degree of freedom is a restriction of this file only.
type Phase = (Double, Double)

-- | [TYPE] Bare object: generator plus the field it induces.  The pair
-- @(generator, field)@ stands in for @(H, X_H)@ under a fixed symplectic
-- form; the form itself is recorded numerically as its matrix, so that a
-- reader can see that changing it changes the object.
data BareObject = BareObject
  { objName   :: String
  , generator :: Phase -> Double
  , field     :: Phase -> Phase
  , formMat   :: ((Double, Double), (Double, Double))
  }

-- | [TYPE] Physical dimension carried by a readout channel.  Units are DATA
-- of the interpretation and are deleted by 'forget'; that deletion is the
-- whole content of "mathematically isomorphic, physically distinct".
data Unit = Metre | Coulomb | Joule | Second | Volt | Named String
  deriving (Eq, Show)

-- | [TYPE] Interpretation @(P, mu, U, epsilon, T)@ of the series.
data Interp = Interp
  { preparable :: Phase -> Bool
  , readoutMap :: Phase -> [Double]
  , unitsOf    :: [Unit]
  , resolution :: Double
  , window     :: Double
  }

-- | [TYPE] A theory object is a bare object together with an interpretation.
data TheoryObject = TheoryObject BareObject Interp

-- | [TYPE] The forgetting operation @U@.  It is total and non-injective on
-- interpretations, which is why empirical claims cannot be recovered from
-- the bare object.
forget :: TheoryObject -> BareObject
forget (TheoryObject b _) = b

-- | [NUM] Do two bare objects agree numerically on a sample?  Sampling can
-- only refute agreement; it cannot establish it.
bareAgreeOn :: [Phase] -> Double -> BareObject -> BareObject -> Bool
bareAgreeOn zs tol b1 b2 =
  all ok zs
  where
    ok z = abs (generator b1 z - generator b2 z) <= tol
        && dist (field b1 z) (field b2 z) <= tol
    dist (a, b) (c, d) = max (abs (a - c)) (abs (b - d))

-- | [DEC] Do two interpretations record the same physical dimensions?
unitsAgree :: Interp -> Interp -> Bool
unitsAgree i1 i2 = unitsOf i1 == unitsOf i2

-- | [DEC] Nondegeneracy and antisymmetry of the recorded 2-form, in the only
-- case this file covers (@dim = 2@).  This is the axiom "symplectic
-- structure" of the reconstruction paper, checked on the matrix that the
-- object carries; closedness is vacuous in dimension two.
formIsSymplectic2D :: BareObject -> Bool
formIsSymplectic2D b = a11 == 0 && a22 == 0 && a12 == negate a21 && a12 /= 0
  where ((a11, a12), (a21, a22)) = formMat b

-- | [NUM] The empirical model @Emp(Th)@ of the reconstruction paper, sampled:
-- preparable states only, readout along the flow, reported at the declared
-- resolution over the declared window.  Everything that distinguishes this
-- from the bare object -- @P@, @mu@, @epsilon@, @T@ -- comes from 'Interp',
-- which 'forget' deletes.
empiricalModel :: TheoryObject -> Double -> [Phase] -> [(Phase, Double, [Double])]
empiricalModel (TheoryObject b i) h zs =
  [ (z, t, map (quantise (resolution i)) (readoutMap i z'))
  | z <- zs
  , preparable i z
  , (t, z') <- zip times (trajectory (field b) h nSteps z) ]
  where
    nSteps = max 0 (floor (window i / h))
    times  = [ fromIntegral n * h | n <- [0 .. nSteps] ]

quantise :: Double -> Double -> Double
quantise eps x = eps * fromIntegral (round (x / eps) :: Integer)

massSpring :: TheoryObject
massSpring = TheoryObject
  (BareObject "mass-spring"
     (\(q, p) -> p * p / (2 * m) + k * q * q / 2)
     (\(q, p) -> (p / m, negate (k * q)))
     ((0, 1), (-1, 0)))
  (Interp (\(q, p) -> abs q <= 1 && abs p <= 1) (\(q, _) -> [q])
          [Metre] 1.0e-4 10)
  where m = 1.0; k = 1.0

-- | Same bare object, different interpretation: @m := L@, @k := 1/C@.
lcCircuit :: TheoryObject
lcCircuit = TheoryObject
  (BareObject "LC-circuit"
     (\(q, p) -> p * p / (2 * l) + q * q / (2 * c))
     (\(q, p) -> (p / l, negate (q / c)))
     ((0, 1), (-1, 0)))
  (Interp (\(q, p) -> abs q <= 1 && abs p <= 1) (\(q, _) -> [q])
          [Coulomb] 1.0e-4 10)
  where l = 1.0; c = 1.0

-- ===================================================================
-- 5.  Numerical illustration of the two separation results      (HR)
-- ===================================================================

-- | [NUM] One RK4 step.  Fourth-order accurate for smooth fields; the error
-- is not tracked, so nothing here is a bound.
rk4 :: (Phase -> Phase) -> Double -> Phase -> Phase
rk4 f h z@(q, p) =
  let (k1q, k1p) = f z
      (k2q, k2p) = f (q + h / 2 * k1q, p + h / 2 * k1p)
      (k3q, k3p) = f (q + h / 2 * k2q, p + h / 2 * k2p)
      (k4q, k4p) = f (q + h * k3q, p + h * k3p)
  in ( q + h / 6 * (k1q + 2 * k2q + 2 * k3q + k4q)
     , p + h / 6 * (k1p + 2 * k2p + 2 * k3p + k4p) )

trajectory :: (Phase -> Phase) -> Double -> Int -> Phase -> [Phase]
trajectory f h n = take (n + 1) . iterate (rk4 f h)

-- | Harmonic field and its quartic perturbation, as in the proposition
-- "empirically equivalent, mathematically non-isomorphic".
harmonicField :: Phase -> Phase
harmonicField (q, p) = (p, negate q)

quarticField :: Double -> Phase -> Phase
quarticField lam (q, p) = (p, negate q - 4 * lam * q * q * q)

-- | Damped field: globally asymptotically stable, hence Hamiltonian for no
-- symplectic form at all (new result of the reconstruction paper).  The check
-- below only exhibits the decay; the impossibility is proved in the paper,
-- not here.
dampedField :: Double -> Phase -> Phase
dampedField gam (q, p) = (p, negate q - gam * p)

-- | [NUM] Sup-norm separation of two trajectories over a window.
sepSup :: (Phase -> Phase) -> (Phase -> Phase) -> Double -> Int -> Phase -> Double
sepSup f g h n z0 =
  maximum (zipWith d (trajectory f h n z0) (trajectory g h n z0))
  where d (a, b) (c, e) = max (abs (a - c)) (abs (b - e))

-- ===================================================================
-- 6.  Empirical layer: outcome laws, tolerance, quotient        (EL)
-- ===================================================================

-- | [TYPE] A finitely supported outcome law.  The empirical-limits paper
-- works with probability kernels; this is the finite case only.
newtype Dist a = Dist [(a, Double)]

massOf :: Eq a => Dist a -> a -> Double
massOf (Dist xs) a = sum [ w | (b, w) <- xs, b == a ]

support :: Eq a => Dist a -> [a]
support (Dist xs) = nub (map fst xs)

-- | [NUM] Total-variation distance between finitely supported laws.
tvDist :: Eq a => Dist a -> Dist a -> Double
tvDist d1 d2 =
  0.5 * sum [ abs (massOf d1 a - massOf d2 a)
            | a <- nub (support d1 ++ support d2) ]

-- | [TYPE] A registered experiment family: a context set and, for each
-- context and model, a predicted outcome law.  This is the @(C, P, Q, K)@
-- data of the empirical-limits paper with the kernels already integrated.
data Experiments m c a = Experiments
  { contexts :: [c]
  , lawOf    :: c -> m -> Dist a
  }

-- | [NUM] Indexed discrepancy @Delta_D@ over the registered contexts.
deltaD :: Eq a => Experiments m c a -> m -> m -> Double
deltaD e m1 m2 = maximum (0 : [ tvDist (lawOf e c m1) (lawOf e c m2) | c <- contexts e ])

-- | [DEC] eta-observational equivalence on the registered domain.
obsEquiv :: Eq a => Experiments m c a -> Double -> m -> m -> Bool
obsEquiv e eta m1 m2 = deltaD e m1 m2 <= eta

-- | [DEC] Observational classes of a finite model class.  This is the
-- computable image of the observational quotient; the Lean file proves the
-- factorization statement that justifies calling it a quotient.
obsClasses :: Eq a => Experiments m c a -> Double -> [m] -> [[m]]
obsClasses e eta = foldl' insert []
  where
    insert [] m = [[m]]
    insert (cl@(representative : _) : cls) m
      | obsEquiv e eta representative m = (m : cl) : cls
      | otherwise                  = cl : insert cls m
    insert ([] : cls) m = [m] : cls

-- | [DEC] Is a property identifiable from the registered experiments?  A
-- False answer is a genuine underdetermination witness on the given class.
identifiable :: (Eq a, Eq z) => Experiments m c a -> Double -> [m] -> (m -> z) -> Bool
identifiable e eta ms phi =
  and [ phi m1 == phi m2 | m1 <- ms, m2 <- ms, obsEquiv e eta m1 m2 ]

-- | [NUM] Uniform error-transfer bound of the empirical-limits paper:
-- @sup_c TV(P_S, P_0) <= sup_c e_lambda(c) + r(lambda)@.  The function
-- returns the right-hand side; it is a bound only under the paper's premise
-- that some family member is already tied to the target by evidence.
errorTransferBound :: Double -> Double -> Double
errorTransferBound supTargetErr uniformModelErr = supTargetErr + uniformModelErr

-- ===================================================================
-- 7.  Checks
-- ===================================================================

data Check = Check { checkName :: String, checkKind :: String, checkPassed :: Bool }

-- Two-state toy models for the empirical layer.
data Toy = ToyA | ToyB | ToyC deriving (Eq, Show)

toyExperiments :: Experiments Toy Int Bool
toyExperiments = Experiments
  { contexts = [0, 1]
  , lawOf = \c m -> case (c, m) of
      (0, _)     -> Dist [(True, 0.5), (False, 0.5)]   -- context 0 separates nothing
      (1, ToyA)  -> Dist [(True, 1.0), (False, 0.0)]
      (1, ToyB)  -> Dist [(True, 0.0), (False, 1.0)]
      (1, ToyC)  -> Dist [(True, 1.0), (False, 0.0)]   -- ToyC is a relabelling of ToyA
      _          -> Dist [(True, 0.5), (False, 0.5)]
  }

restrictedExperiments :: Experiments Toy Int Bool
restrictedExperiments = toyExperiments { contexts = [0] }

counter :: Sys () Int Int
counter = Sys { step = \_ x -> x + 1, readout = id }

doubler :: Sys () Int Int
doubler = Sys { step = \_ x -> 2 * x, readout = id }

adder :: Sys Int Int Int
adder = Sys { step = \i x -> x + i, readout = id }

coupledSys :: Sys () (Int, Int) (Int, Int)
coupledSys = Sys { step = \_ (x, y) -> (x + y, y), readout = id }

checks :: [Check]
checks =
  [ Check "product run factors (Lean: runPar)" "DEC"
      (runParFactors counter doubler (replicate 6 ((), ())) (3, 5))

  , Check "par is non-interacting on the sample" "DEC"
      (nonInteractingOn [((), ())] [0 .. 3 :: Int] [0 .. 3 :: Int] (par counter doubler))

  , Check "serial composition reads the updated upstream output" "DEC"
      (let sc = serial counter adder
       in readout sc (runSys sc [(), ()] (0, 0)) == 3)   -- 1 then 2; the
         -- asynchronous convention would give 0 + 1 = 1, so the timing
         -- convention is observable and therefore part of the theory.

  , Check "coupled system is detected as interacting" "DEC"
      (not (nonInteractingOn [()] [0 .. 3 :: Int] [0 .. 3 :: Int] coupledSys))

  , Check "additive coupling passes the separability test" "DEC"
      (separableOn [0 .. 4] [0 .. 4] (\a b -> 3 * a + 2 * b))

  , Check "product coupling fails it (interaction)" "DEC"
      (not (separableOn [0 .. 4] [0 .. 4] (\a b -> a * b)))

  , Check "split witness reproduces the separable coupling" "DEC"
      (case splitCoupling [0 .. 4] [0 .. 4] (\a b -> 3 * a + 2 * b) of
         Nothing     -> False
         Just (f, g) -> and [ f a + g b == 3 * a + 2 * b | a <- [0 .. 4], b <- [0 .. 4] ])

  , Check "zero-period form has a potential" "DEC"
      (case potential 4 (\k -> [1, -1, 2, -2] !! (k `mod` 4)) of
         Nothing -> False
         Just h  -> and [ diffSeq h k == [1, -1, 2, -2] !! (k `mod` 4) | k <- [0 .. 3] ]
                    && h 4 == h 0)

  , Check "unit-period form has none (torus obstruction)" "DEC"
      (case potential 4 (const 1) of Nothing -> True; Just _ -> False)

  , Check "additive constant is invisible to the difference" "DEC"
      (and [ diffSeq (\k -> fromIntegral k * fromIntegral k) j
               == diffSeq (\k -> fromIntegral k * fromIntegral k + 7) j
           | j <- [0 .. 20] ])

  , Check "bare objects of mass-spring and LC agree numerically" "NUM"
      (bareAgreeOn [(q, p) | q <- [-1, -0.5, 0, 0.5, 1], p <- [-1, 0, 1]] 1.0e-12
         (forget massSpring) (forget lcCircuit))

  , Check "their interpretations do not (metre vs coulomb)" "DEC"
      (not (unitsAgree (interpOf massSpring) (interpOf lcCircuit)))

  , Check "both recorded 2-forms are antisymmetric and nondegenerate" "DEC"
      (formIsSymplectic2D (forget massSpring) && formIsSymplectic2D (forget lcCircuit))

  , Check "Emp(Th) is nonempty and respects the declared resolution" "NUM"
      (let recs = empiricalModel massSpring 0.05 [(0.5, 0.0), (2.0, 0.0)]
           eps  = resolution (interpOf massSpring)
       in not (null recs)
          && all (\(_, _, ys) -> all (\y -> abs (y - quantise eps y) < 1.0e-15) ys) recs
          && all (\(z, _, _) -> preparable (interpOf massSpring) z) recs)

  , Check "forget keeps the name and drops the units" "DEC"
      (objName (forget massSpring) == "mass-spring"
       && objName (forget lcCircuit) == "LC-circuit")

  , Check "small quartic term stays within tolerance on [0,T]" "NUM"
      (sepSup harmonicField (quarticField 1.0e-4) 0.01 1000 (1, 0) < 1.0e-2)

  , Check "large quartic term leaves it (equivalence is indexed)" "NUM"
      (sepSup harmonicField (quarticField 0.5) 0.01 1000 (1, 0) > 1.0e-2)

  , Check "damped trajectory decays towards the equilibrium" "NUM"
      (let z0 = (1, 0)
           zs = trajectory (dampedField 0.3) 0.01 4000 z0
           nrm (q, p) = sqrt (q * q + p * p)
       in case reverse zs of
            zLast : _ -> nrm zLast < 0.05 * nrm z0
            [] -> False)

  , Check "restricting contexts cannot separate more models" "DEC"
      (deltaD restrictedExperiments ToyA ToyB <= deltaD toyExperiments ToyA ToyB)

  , Check "ToyA and ToyC are observationally identified" "DEC"
      (obsEquiv toyExperiments 0 ToyA ToyC)

  , Check "the registered family has exactly two classes" "DEC"
      (length (obsClasses toyExperiments 0 [ToyA, ToyB, ToyC]) == 2)

  , Check "a label distinguishing ToyA from ToyC is not identifiable" "DEC"
      (not (identifiable toyExperiments 0 [ToyA, ToyB, ToyC] show))

  , Check "the outcome law itself is identifiable" "DEC"
      (identifiable toyExperiments 0 [ToyA, ToyB, ToyC]
         (\m -> map (\c -> massOf (lawOf toyExperiments c m) True) (contexts toyExperiments)))

  , Check "error transfer respects the triangle inequality" "NUM"
      (let dSM = tvDist (Dist [(True, 0.7), (False, 0.3)]) (Dist [(True, 0.6), (False, 0.4)])
           dM0 = tvDist (Dist [(True, 0.6), (False, 0.4)]) (Dist [(True, 0.5), (False, 0.5)])
           dS0 = tvDist (Dist [(True, 0.7), (False, 0.3)]) (Dist [(True, 0.5), (False, 0.5)])
       in dS0 <= errorTransferBound dSM dM0 + 1.0e-12)
  ]
  where
    interpOf (TheoryObject _ i) = i

main :: IO ()
main = do
  putStrLn "PRINCIPIA PHYSICA -- Core.hs checks"
  putStrLn "DEC = exact on the stated finite data; NUM = floating-point illustration."
  putStrLn (replicate 68 '-')
  forM_ checks $ \c ->
    printf "%-5s %-4s %s\n" (if checkPassed c then "PASS" else "FAIL")
           (checkKind c) (checkName c)
  let failed = length (filter (not . checkPassed) checks)
  putStrLn (replicate 68 '-')
  printf "%d checks, %d failed\n" (length checks) failed
  putStrLn "No check above proves a theorem of the series; see the header."
  unless (failed == 0) exitFailure
  exitSuccess
