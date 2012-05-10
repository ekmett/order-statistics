{-# LANGUAGE TypeFamilies, PatternGuards #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Statistics.Order
-- Copyright   :  (C) 2012 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Haskell 2011 + TypeFamilies
--
----------------------------------------------------------------------------

module Statistics.Order
  (
  -- * L-Estimator
    L(..)
  -- ** Applying an L-estimator
  , (@@), (@!)
  -- ** Analyzing an L-estimator
  , (@#)
  , breakdown
  -- ** Robust L-Estimators
  , trimean  -- Tukey's trimean
  , midhinge -- average of q1 and q3
  , iqr      -- interquartile range
  , iqm      -- interquartile mean
  , lscale   -- second L-moment
  -- ** L-Estimator Combinators
  , trimmed
  , winsorized, winsorised
  , jackknifed
  -- ** Trivial L-Estimators
  , mean
  , total
  , lmin, lmax
  , midrange
  -- ** Sample-size-dependent L-Estimators
  , nthSmallest
  , nthLargest
  -- ** Quantiles
  -- *** Common quantiles
  , quantile
  , median
  , tercile, t1, t2
  , quartile, q1, q2, q3
  , quintile, qu1, qu2, qu3, qu4
  , percentile
  , permille
  -- *** Harrell-Davis Quantile Estimator
  , hdquantile
  -- *** Compute a quantile using a specified quantile estimation strategy
  , quantileBy
  -- * Sample Quantile Estimators
  , Estimator
  , Estimate(..)
  , r1,r2,r3,r4,r5,r6,r7,r8,r9,r10
  ) where

import Data.Ratio
import Data.List (sort)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Vector (Vector, (!))
import qualified Data.Vector as V
import Data.VectorSpace
import Statistics.Distribution.Beta
import qualified Statistics.Distribution as D

-- | L-estimators are linear combinations of order statistics used by 'robust' statistics.
newtype L r = L { runL :: Int -> IntMap r }

-- TODO: Write code to test if the result of a given L-estimator will be always than or equal 
-- to the result of another L-estimator at a given sample size.

-- | Calculate the result of applying an L-estimator after sorting list into order statistics
(@@) :: (Num r, Ord r) => L r -> [r] -> r
l @@ xs = l @! V.fromList (sort xs)

-- | Calculate the result of applying an L-estimator to a *pre-sorted* vector of order statistics
(@!) :: Num r => L r -> Vector r -> r
L f @! v = IM.foldrWithKey (\k x y -> (v ! k) * x + y) 0 $ f (V.length v)

-- | get a vector of the coefficients of an L estimator when applied to an input of a given length
(@#) :: Num r => L r -> Int -> [r]
L f @# n = map (\k -> IM.findWithDefault 0 k fn) [0..n-1] where fn = f n

-- | calculate the breakdown % of an L-estimator
breakdown :: (Num r, Eq r) => L r -> Int
breakdown (L f)
  | IM.null m = 50
  | otherwise = fst (IM.findMin m) `min` (100 - fst (IM.findMax m))
  where m = IM.filter (/= 0) $ f 101

instance Num r => AdditiveGroup (L r) where
  zeroV = L $ \_ -> IM.empty
  L fa ^+^ L fb = L $ \n -> IM.unionWith (+) (fa n) (fb n)
  negateV (L fa) = L $ fmap negate . fa

instance Num r => VectorSpace (L r) where
  type Scalar (L r) = r
  x *^ L y = L $ fmap (x *) . y

clamp :: Int -> Int -> Int
clamp n k
  | k <= 0 = 0
  | k >= n = n - 1
  | otherwise = k

-- | The average of all of the order statistics. Not robust.
--
-- > breakdown mean = 0%
mean :: Fractional r => L r
mean = L $ \n -> IM.fromList [ (i, 1 / fromIntegral n) | i <- [0..n-1]]

-- | The sum of all of the order statistics. Not robust.
--
-- > breakdown total = 0%
total :: Num r => L r
total = L $ \n -> IM.fromList [ (i, 1) | i <- [0..n-1]]

-- | Calculate a trimmed L-estimator. If the sample size isn't evenly divided, linear interpolation is used
-- as described in <http://en.wikipedia.org/wiki/Trimmed_mean#Interpolation>

-- Trimming can increase the robustness of a statistic by removing outliers.

trimmed :: Fractional r => Rational -> L r -> L r
trimmed p (L g) = L $ \n -> case properFraction (fromIntegral n * p) of
  (w, 0)               -> IM.fromDistinctAscList [ (k + w, v)                        | (k,v) <- IM.toAscList $ g (n - w*2)]
  (w, f) | w' <- w + 1 -> IM.fromListWith (+) $  [ (k + w, fromRational (1 - f) * v) | (k,v) <- IM.toList $ g (n - w*2)] ++
                                                 [ (k + w', fromRational f  * v)     | (k,v) <- IM.toList $ g (n - w'*2)]

-- | Calculates an interpolated winsorized L-estimator in a manner analogous to the trimmed estimator. 
-- Unlike trimming, winsorizing replaces the extreme values.
winsorized, winsorised :: Fractional r => Rational -> L r -> L r
winsorised = winsorized
winsorized p (L g) = L $ \n -> case properFraction (fromIntegral n * p) of
  (w, 0)               -> IM.fromAscListWith (+) [ (w `max` min (n - 1 - w) k, v) | (k,v) <- IM.toAscList (g n) ]
  (w, f) | w' <- w + 1 -> IM.fromListWith (+) $ do
     (k,v) <- IM.toList (g n)
     [ (w  `max` min (n - 1 - w ) k, v * fromRational (1 - f)),
       (w' `max` min (n - 1 - w') k, v * fromRational f)]

-- | Jackknifes the statistic by removing each sample in turn and recalculating the L-estimator,
-- requires at least 2 samples!
jackknifed :: Fractional r => L r -> L r
jackknifed (L g) = L $ \n -> IM.fromAscListWith (+) $ do
  let n' = fromIntegral n
  (k,v) <- IM.toAscList (g (n - 1))
  let k' = fromIntegral k + 1
  [(k, (n' - k') * v / n'), (k + 1, k' * v / n')]

-- | The most robust L-estimator possible.
--
-- > breakdown median = 50
median :: Fractional r => L r
median = L go where
  go n
    | odd n        = IM.singleton (div (n - 1) 2) 1
    | k <- div n 2 = IM.fromList [(k-1, 0.5), (k, 0.5)]

-- | Sample quantile estimators
data Estimate r  = Estimate {-# UNPACK #-} !Rational (IntMap r)
type Estimator r = Rational -> Int -> Estimate r

-- | Compute a quantile using the given estimation strategy to interpolate when an exact quantile isn't available
quantileBy :: Num r => Estimator r -> Rational -> L r
quantileBy f p = L $ \n -> case f p n of
  Estimate h qp -> case properFraction h of
    (w, 0) -> IM.singleton (clamp n (w - 1)) 1
    _      -> qp

-- | Compute a quantile with traditional direct averaging
quantile :: Fractional r => Rational -> L r
quantile = quantileBy r2

tercile :: Fractional r => Rational -> L r
tercile n = quantile (n/3)

-- | terciles 1 and 2
--
-- > breakdown t1 = breakdown t2 = 33%
t1, t2 :: Fractional r => L r
t1 = quantile (1/3)
t2 = quantile (2/3)

quartile :: Fractional r => Rational -> L r
quartile n = quantile (n/4)

-- | quantiles, with breakdown points 25%, 50%, and 25% respectively
q1, q2, q3 :: Fractional r => L r
q1 = quantile 0.25
q2 = median
q3 = quantile 0.75

quintile :: Fractional r => Rational -> L r
quintile n = quantile (n/5)

-- | quintiles 1 through 4
qu1, qu2, qu3, qu4 :: Fractional r => L r
qu1 = quintile 1
qu2 = quintile 2
qu3 = quintile 3
qu4 = quintile 4

-- |
--
-- > breakdown (percentile n) = min n (100 - n)
percentile :: Fractional r => Rational -> L r
percentile n = quantile (n/100)

permille :: Fractional r => Rational -> L r
permille n = quantile (n/1000)

nthSmallest :: Num r => Int -> L r
nthSmallest k = L $ \n -> IM.singleton (clamp n k) 1

nthLargest :: Num r => Int -> L r
nthLargest k = L $ \n -> IM.singleton (clamp n (n - 1 - k)) 1

-- |
--
-- > midhinge = trimmed 0.25 midrange
-- > breakdown midhinge = 25%
midhinge :: Fractional r => L r
midhinge = (q1 ^+^ q3) ^/ 2

-- | Tukey's trimean
--
-- > breakdown trimean = 25
trimean :: Fractional r => L r
trimean = (q1 ^+^ 2 *^ q2 ^+^ q3) ^/ 4

-- | The maximum value in the sample
lmax :: Num r => L r
lmax = L $ \n -> IM.singleton (n-1) 1

-- | The minimum value in the sample
lmin :: Num r => L r
lmin = L $ \_ -> IM.singleton 0 1

-- |
-- > midrange = lmax - lmin
-- > breakdown midrange = 0%
midrange :: Fractional r => L r
midrange = L $ \n -> IM.fromList [(0,-1),(n-1,1)]

-- | interquartile range
--
-- > breakdown iqr = 25%
-- > iqr = trimmed 0.25 midrange
iqr :: Fractional r => L r
iqr = q3 ^-^ q1

-- | interquartile mean
--
-- > iqm = trimmed 0.25 mean
iqm :: Fractional r => L r
iqm = trimmed 0.25 mean

-- | Direct estimator for the second L-moment given a sample
lscale :: Fractional r => L r
lscale = L $ \n -> let
     r = fromIntegral n
     scale = 1 / (r * (r-1))
  in IM.fromList [ (i - 1, scale * (2 * fromIntegral i - 1 - r)) | i <- [1..n] ]

-- | The Harrell-Davis quantile estimate. Uses multiple order statistics to approximate the quantile
-- to reduce variance.
hdquantile :: Fractional r => Rational -> L r
hdquantile q = L $ \n ->
  let n' = fromIntegral n
      np1 = n' + 1
      q' = fromRational q
      d = betaDistr (q'*np1) (np1*(1-q')) in
  if q == 0 then IM.singleton 0 1
  else if q == 1 then IM.singleton (n - 1) 1
  else IM.fromAscList
    [ (i, realToFrac $ D.cumulative d ((fromIntegral i + 1) / n') -
                       D.cumulative d (fromIntegral i / n'))
    | i <- [0 .. n - 1]
    ]

-- More information on the individual estimators used below can be found in:
-- http://stat.ethz.ch/R-manual/R-devel/library/stats/html/quantile.html
-- and
-- http://en.wikipedia.org/wiki/Quantile#Estimating_the_quantiles_of_a_population

-- | Inverse of the empirical distribution function
r1 :: Num r => Estimator r
r1 p n = Estimate (np + 1%2) $ IM.singleton (clamp n (ceiling np - 1)) 1
  where np = fromIntegral n * p

-- | .. with averaging at discontinuities
r2 :: Fractional r => Estimator r
r2 p n =  Estimate (np + 1%2) $
  if p == 0      then IM.singleton 0       1
  else if p == 1 then IM.singleton (n - 1) 1
  else IM.fromList [(ceiling np - 1, 0.5), (floor np, 0.5)]
  where np = fromIntegral n * p

-- | The observation numbered closest to Np. NB: does not yield a proper median
r3 :: Num r => Estimator r
r3 p n = Estimate np $ IM.singleton (clamp n (round np - 1)) 1
  where np = fromIntegral n * p

-- continuous sample quantiles
continuousEstimator ::
  Fractional r =>
  (Rational -> (Rational, Rational)) -> -- take the number of samples, and return upper and lower bounds on 'p = k/n' for which this interpolation should be used
  (Rational -> Rational -> Rational) -> -- take p = k/q, and n the number of samples, and return the coefficient h which will be used for interpolation when h is not integral
  Estimator r
continuousEstimator bds f p n = Estimate h $
  if p < lo then IM.singleton 0 1
  else if p >= hi then IM.singleton (n - 1) 1
  else case properFraction h of
    (w,frac) | frac' <- fromRational frac -> IM.fromList [(w - 1, frac'), (w, 1 - frac')]
  where
    r = fromIntegral n
    h = f p r
    (lo, hi) = bds r

-- | Linear interpolation of the empirical distribution function. NB: does not yield a proper median.
r4 :: Fractional r => Estimator r
r4 = continuousEstimator (\n -> (1 / n, 1)) (*)

-- | .. with knots midway through the steps as used in hydrology. This is the simplest continuous estimator that yields a correct median
r5 :: Fractional r => Estimator r
r5 = continuousEstimator (\n -> let tn = 2 * n in (1 / tn, (tn - 1) / tn)) $ \p n -> p*n + 0.5

-- | Linear interpolation of the expectations of the order statistics for the uniform distribution on [0,1]
r6 :: Fractional r => Estimator r
r6 = continuousEstimator (\n -> (1 / (n + 1), n / (n + 1))) $ \p n -> p*(n+1)

-- | Linear interpolation of the modes for the order statistics for the uniform distribution on [0,1]
r7 :: Fractional r => Estimator r
r7 = continuousEstimator (\_ -> (0, 1)) $ \p n -> p*(n-1) + 1

-- | Linear interpolation of the approximate medans for order statistics.
r8 :: Fractional r => Estimator r
r8 = continuousEstimator (\n -> (2/3 / (n + 1/3), (n - 1/3)/(n + 1/3))) $ \p n -> p*(n + 1/3) + 1/3

-- | The resulting quantile estimates are approximately unbiased for the expected order statistics if x is normally distributed.
r9 :: Fractional r => Estimator r
r9 = continuousEstimator (\n -> (0.625 / (n + 0.25), (n - 0.375)/(n + 0.25))) $ \p n -> p*(n + 0.25) + 0.375

-- | When rounding h, this yields the order statistic with the least expected square deviation relative to p.
r10 :: Fractional r => Estimator r
r10 = continuousEstimator (\n -> (1.5 / (n + 2), (n + 0.5)/(n + 2))) $ \p n -> p*(n + 2) - 0.5

