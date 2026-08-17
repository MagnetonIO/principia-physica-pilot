-- | A small executable vocabulary for the formal appendix.
--
-- The types deliberately keep mathematical structure, empirical
-- interpretation, and evidence for equivalence separate.  They do not attempt
-- to prove smoothness, symplecticity, or Hamilton's equations: those remain
-- obligations on values supplied by a user of this module.
module Core
  ( Observable (..)
  , VectorField
  , LocalFlow
  , BareModel (..)
  , Procedure (..)
  , Interpretation (..)
  , InterpretedModel (..)
  , ProductState
  , nonInteractingProduct
  , withInteraction
  , sample
  , discrepancy
  , observationallyEquivalent
  , ToleranceWitness (..)
  , toleranceWitness
  , Preservation (..)
  , EquivalenceCertificate (..)
  , physicallyEquivalent
  ) where

-- | A real-valued mathematical observable.  Units and instrument semantics
-- belong to 'Procedure', not to this wrapper.
newtype Observable state = Observable
  { evaluate :: state -> Double
  }

-- | A coordinate representation of a vector field.  The module cannot check
-- that it is smooth or Hamiltonian for a supplied symplectic form.
type VectorField state = state -> state

-- | A possibly local flow: 'Nothing' records that the requested time/state is
-- outside its domain.  This avoids silently assuming completeness.
type LocalFlow state = Double -> state -> Maybe state

-- | Computational data associated with a bare Hamiltonian theory object.
-- The symplectic form is represented indirectly by the documented obligation
-- that @modelVectorField@ is the Hamiltonian field of @modelHamiltonian@.
data BareModel state = BareModel
  { modelHamiltonian :: Observable state
  , modelVectorField :: VectorField state
  , modelFlow :: LocalFlow state
  }

-- | Laboratory meaning attached to a designated mathematical observable.
data Procedure state = Procedure
  { procedureName :: String
  , procedureUnit :: String
  , procedureResolution :: Double
  , procedureObservable :: Observable state
  }

-- | Empirical structure not recoverable from a bare model.
data Interpretation protocol state = Interpretation
  { procedures :: [Procedure state]
  , prepare :: protocol -> [state]
  , clockCalibration :: Double -> Double
  }

data InterpretedModel protocol state = InterpretedModel
  { bareModel :: BareModel state
  , interpretation :: Interpretation protocol state
  }

type ProductState left right = (left, right)

-- | Kinematic product with additive Hamiltonian and componentwise free flow.
-- It represents parallel, non-interacting composition only.
nonInteractingProduct
  :: BareModel left
  -> BareModel right
  -> BareModel (ProductState left right)
nonInteractingProduct left right = BareModel
  { modelHamiltonian = Observable $ \(x, y) ->
      evaluate (modelHamiltonian left) x
        + evaluate (modelHamiltonian right) y
  , modelVectorField = \(x, y) ->
      (modelVectorField left x, modelVectorField right y)
  , modelFlow = \time (x, y) -> do
      x' <- modelFlow left time x
      y' <- modelFlow right time y
      pure (x', y')
  }

-- | Add interaction data to a product.  The coupled field and flow are extra
-- data because an interaction Hamiltonian alone is insufficient here to
-- compute its Hamiltonian vector field without a concrete symplectic backend.
withInteraction
  :: Observable (ProductState left right)
  -> VectorField (ProductState left right)
  -> LocalFlow (ProductState left right)
  -> BareModel (ProductState left right)
  -> BareModel (ProductState left right)
withInteraction interactionHamiltonian coupledField coupledFlow freeModel =
  freeModel
    { modelHamiltonian = Observable $ \state ->
        evaluate (modelHamiltonian freeModel) state
          + evaluate interactionHamiltonian state
    , modelVectorField = coupledField
    , modelFlow = coupledFlow
    }

-- | Evaluate a procedure along a local flow.  Calibrated times for which the
-- flow is undefined are represented by 'Nothing'.
sample
  :: InterpretedModel protocol state
  -> Procedure state
  -> state
  -> [Double]
  -> [Maybe Double]
sample interpreted procedure initialState =
  map $ \instrumentTime -> do
    let calibratedTime =
          clockCalibration (interpretation interpreted) instrumentTime
    state <- modelFlow (bareModel interpreted) calibratedTime initialState
    pure (evaluate (procedureObservable procedure) state)

-- | Supremum discrepancy on a supplied finite observation grid.  An empty
-- grid has zero discrepancy; incompatible sample shapes or undefined samples
-- have no discrepancy value.
discrepancy :: [Maybe Double] -> [Maybe Double] -> Maybe Double
discrepancy left right
  | length left /= length right = Nothing
  | otherwise = foldl' step (Just 0) (zip left right)
  where
    step :: Maybe Double -> (Maybe Double, Maybe Double) -> Maybe Double
    step current (Just x, Just y) = max (abs (x - y)) <$> current
    step _ _ = Nothing

-- | Finite-grid observational equivalence.  This is intentionally a tolerance
-- predicate, not a Haskell 'Eq' instance: for positive tolerance it need not
-- be transitive.
observationallyEquivalent
  :: Double
  -> [Maybe Double]
  -> [Maybe Double]
  -> Bool
observationallyEquivalent epsilon left right =
  epsilon >= 0 && maybe False (<= epsilon) (discrepancy left right)

-- | Concrete evidence that tolerance-based observational equivalence is not
-- transitive: adjacent readings pass while the endpoints fail.
data ToleranceWitness = ToleranceWitness
  { witnessLeft :: Double
  , witnessMiddle :: Double
  , witnessRight :: Double
  , witnessTolerance :: Double
  }
  deriving (Eq, Show)

toleranceWitness :: Double -> Maybe ToleranceWitness
toleranceWitness epsilon
  | epsilon > 0 = Just ToleranceWitness
      { witnessLeft = 0
      , witnessMiddle = epsilon
      , witnessRight = 2 * epsilon
      , witnessTolerance = epsilon
      }
  | otherwise = Nothing

-- | What a proposed model map is claimed to preserve.  Interpretation is an
-- explicit field rather than an automatic consequence of dynamics.
data Preservation = Preservation
  { preservesSymplecticStructure :: Bool
  , preservesHamiltonian :: Bool
  , preservesDynamics :: Bool
  , preservesInterpretation :: Bool
  }
  deriving (Eq, Show)

-- | A preservation-and-loss analysis for an equivalence claim.
data EquivalenceCertificate = EquivalenceCertificate
  { preservation :: Preservation
  , knownLosses :: [String]
  }
  deriving (Eq, Show)

-- | The conservative criterion used by this appendix.  Bare mathematical
-- equivalence alone cannot establish physical equivalence.
physicallyEquivalent :: EquivalenceCertificate -> Bool
physicallyEquivalent certificate =
  let claims = preservation certificate
  in preservesSymplecticStructure claims
      && preservesHamiltonian claims
      && preservesDynamics claims
      && preservesInterpretation claims
      && null (knownLosses certificate)
