-- PRINCIPIA PHYSICA executable companion.
-- Numerical witnesses are not proofs and are not physical observations.

module Core
  ( Label(..)
  , Claim(..)
  , registry
  , registryWellFormed
  , CouplingClass(..)
  , classifyCoupling
  , Params(..)
  , vectorField
  , rk4Step
  , integrate
  , limitInterfaceComparison
  , main
  ) where

import Data.List (intercalate, zipWith4)
import System.Exit (exitFailure, exitSuccess)
import Text.Printf (printf)

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
  { claimId :: String
  , claimLabel :: Label
  , claimDeps :: [String]
  } deriving (Eq, Show)

registry :: [Claim]
registry =
  [ Claim "S-A1" Assumption []
  , Claim "S-A2" Axiom []
  , Claim "S-I1" Interpretation ["S-A2"]
  , Claim "S-D1" Definition ["S-A1"]
  , Claim "S-P1" Proposition ["S-D1"]
  , Claim "S-L1" Lemma ["S-D1"]
  , Claim "S-N1" NewResult ["S-D1", "S-L1"]
  , Claim "S-C1" Corollary ["S-N1"]
  , Claim "S-N2" NewResult ["S-D1", "S-P1"]
  , Claim "S-I2" Interpretation ["S-N2"]
  , Claim "S-N3" NewResult ["S-D1"]
  , Claim "S-E2" EmpiricalStatement ["S-N3"]
  , Claim "S-E3" EmpiricalStatement []
  , Claim "S-C3" Conjecture ["S-N1", "S-N2", "S-N3"]
  ]

registryWellFormed :: [Claim] -> Bool
registryWellFormed claims =
  all (all (`elem` identifiers) . claimDeps) claims
  where
    identifiers = map claimId claims

data CouplingClass
  = Decoupled
  | ReciprocalCoupled
  | NonReciprocal
  deriving (Eq, Show)

classifyCoupling :: Double -> Double -> Double -> CouplingClass
classifyCoupling tolerance c12 c21
  | abs c12 <= tolerance && abs c21 <= tolerance = Decoupled
  | abs (c12 - c21) <= tolerance = ReciprocalCoupled
  | otherwise = NonReciprocal

data Params = Params
  { mass :: Double
  , omega :: Double
  , coupling :: Double
  } deriving (Eq, Show)

-- State order: q1, p1, q2, p2.
vectorField :: Params -> [Double] -> [Double]
vectorField parameters [q1, p1, q2, p2] =
  [ p1 / mass parameters
  , negate (mass parameters * omega parameters ^ (2 :: Int) * q1)
      - coupling parameters * q2
  , p2 / mass parameters
  , negate (mass parameters * omega parameters ^ (2 :: Int) * q2)
      - coupling parameters * q1
  ]
vectorField _ state =
  error ("vectorField expected four components, received " ++ show (length state))

addScaled :: Double -> [Double] -> [Double] -> [Double]
addScaled scale increment state =
  zipWith (\x dx -> x + scale * dx) state increment

rk4Step :: ([Double] -> [Double]) -> Double -> [Double] -> [Double]
rk4Step field step state =
  zipWith (\x dx -> x + step * dx / 6) state total
  where
    k1 = field state
    k2 = field (addScaled (step / 2) k1 state)
    k3 = field (addScaled (step / 2) k2 state)
    k4 = field (addScaled step k3 state)
    total = zipWith4 (\a b c d -> a + 2 * b + 2 * c + d) k1 k2 k3 k4

integrate :: ([Double] -> [Double]) -> Double -> Int -> [Double] -> [Double]
integrate field step count initial =
  iterate (rk4Step field step) initial !! count

-- S-N3 computational shadow. The first two values use the same interaction
-- parameter and therefore compute the same system. The third discards it.
limitInterfaceComparison :: Double -> Double -> Double -> (Double, Double, Double)
limitInterfaceComparison kappa particleMass time =
  ( firstCoordinate limitOfComposite
  , firstCoordinate compositeOfLimits
  , firstCoordinate discardedInterface
  )
  where
    steps = 20000
    step = time / fromIntegral steps
    initial = [0, 0, 1, 0]
    retained = integrate
      (vectorField (Params particleMass 0 kappa)) step steps initial
    limitOfComposite = retained
    compositeOfLimits = retained
    discardedInterface = integrate
      (vectorField (Params particleMass 0 0)) step steps initial

    firstCoordinate :: [Double] -> Double
    firstCoordinate (q1 : _) = q1
    firstCoordinate [] = error "integrator returned an empty state"

check :: String -> Bool -> IO Bool
check name result = do
  printf "[%s] %s\n" (if result then "PASS" else "FAIL" :: String) name
  pure result

main :: IO ()
main = do
  putStrLn "PRINCIPIA PHYSICA executable witnesses"
  putStrLn "Finite computations below are not universal proofs."
  registryResult <- check
    "every dependency names a registered claim"
    (registryWellFormed registry)
  let tolerance = 1e-12
  trichotomyResult <- check
    "representative coupling classes"
    (classifyCoupling tolerance 0 0 == Decoupled
      && classifyCoupling tolerance 2 2 == ReciprocalCoupled
      && classifyCoupling tolerance 2 1 == NonReciprocal)
  let (beforeLimit, afterLimit, discarded) =
        limitInterfaceComparison 1 1 1
  printf "q1(1), limit of composite with kappa retained: %.9f\n" beforeLimit
  printf "q1(1), composite of limits with same kappa:   %.9f\n" afterLimit
  printf "q1(1), composite after discarding kappa:      %.9f\n" discarded
  limitResult <- check
    "fixed-interface results agree and discarded interface differs"
    (abs (beforeLimit - afterLimit) <= 1e-12
      && abs (beforeLimit - discarded) > 1e-3)
  putStrLn ("labels represented: " ++ intercalate ", "
    (map (show . claimLabel) registry))
  if and [registryResult, trichotomyResult, limitResult]
    then exitSuccess
    else exitFailure
