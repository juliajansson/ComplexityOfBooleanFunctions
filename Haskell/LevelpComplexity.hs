{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RebindableSyntax #-}
module LevelpComplexity where
import qualified Prelude
import Prelude hiding (Num(..),Fractional(..), fromIntegral, sum, product)
import Data.List (intersperse)
import DSLsofMath.PSDS
import Alg
---------------- CALCULATION OF EXPECTATION ----------------
probability :: (Foldable t, Functor t, Ring a) => t Bool -> Poly a
probability = product . fmap bool2Prob -- gives a polynomial of degree length of list

instance Foldable (Tup n) where foldr = foldrTup
foldrTup :: (a -> b -> b) -> b -> Tup n a -> b
foldrTup op e (T as) = foldr op e as

product :: (Foldable t, Multiplicative a) => t a -> a
product = foldr (*) one

bool2Prob :: Ring a => Bool -> Poly a
bool2Prob b =  if b then xP else 1-xP
-- xP    = P [0, 1]
-- 1-xP  = P [1,-1]

testProbL :: Ring a => [Poly a]
testProbL = map probability (univ :: [Tuple Three])

-- See below for a smarter (more efficient) way: compute the
-- polynomial while evaluating the algorithm to a "Don" at level k,
-- instead of computing all of those terms.

expectation  :: (Fin (Tuple n), Ring a) => Alg n -> Poly a
expectation = sumProd . expectationStep
expectationStep :: (Fin (Tuple n), Ring a) => Alg n -> [(Int, Poly a)]
expectationStep alg = map (\tup -> (cost alg tup, probability tup)) univ
--  where allTup = univ :: [Tuple n]

sumProd :: (Integral i, Ring a) => [(i, a)] -> a
sumProd = sum . map (\(i, a)-> fromIntegral i * a)

alg2Poly :: (KnownNat n, Ring a) => Alg n -> Poly a
alg2Poly alg = alg2PolyHelp nN 0 one alg
  where nN = fromIntegral (natVal (alg2Proxy alg))

-- Smart expectation: computes the polynomial while evaluating the
-- cost of the algorithm. It accumulates the polynomial as it recurses
-- down and counts the levels (the cost). When it stops at a "Don" at
-- level k, it already knows the expectation of 2^(n-k) terms is just
-- the level (cost) k. No need to compute all of those terms. Can
-- compute expectations for much bigger functions, as long as the
-- algorithm (tree) is reasonably small.

alg2PolyHelp :: (Ring a) => Int -> Int -> Poly a -> Alg n -> Poly a
alg2PolyHelp n level polySoFar (Res _) = scaleP (fromIntegral level) polySoFar
alg2PolyHelp n level polySoFar (Pick i aF aT) = pF + pT
  where pF = alg2PolyHelp n (1+level) ((1-xP)*polySoFar) aF
        pT = alg2PolyHelp n (1+level) (   xP *polySoFar) aT

  -- (scaleP (2^+(n-level)) polySoFar) -- would also be needed if we
  -- counted instead of computed the expected value.

algBore1 :: KnownNat n => Alg (S n)
algBore1 = pick 1 dt df

algHelp :: KnownNat n => Alg n -> Alg (S n)
algHelp a = pick 2 dt a


funTest :: Ring a => Poly a
funTest  = alg2Poly    (algHelp algBore1 :: Alg 15)
funTest' :: Ring a => Poly a
funTest' = expectation (algHelp algBore1 :: Alg 15)
-- expectation takes much longer


{-
λ> p1 = alg2Poly algABC
λ> p1
P [6,-5,-19,62,-60,24,0,0,0]
λ> p2 = expectation algABC
λ> p2
P [6,-5,-19,62,-60,24,0,0,0]
λ> eqPoly p1 2
True

checkExpectation :: Alg n -> Bool
checkExpectation alg = eqPoly (alg2Poly alg) (expectation alg)
-- a bit too polymorphic to test in general
-}

eqPoly :: (Additive a, Eq a) => Poly a -> Poly a -> Bool
eqPoly (P as) (P bs) = eqCoeffList as bs

isZero :: (Additive a, Eq a) => a -> Bool
isZero = (zero==)

eqCoeffList :: (Additive a, Eq a) => [a] -> [a] -> Bool
eqCoeffList xs [] = all isZero xs
eqCoeffList [] ys = all isZero ys
eqCoeffList (x:xs) (y:ys) = x==y && eqCoeffList xs ys

instance (Eq a, Additive a) => Eq (Poly a) where (==) = eqPoly

printPoly :: Poly Int -> String
printPoly (P as) = concat (intersperse "+" [show (as!!i) ++ "p^" ++ show i
                                           | i <- [0..(length as-1)]
                                           ]) ++ ";\n"

