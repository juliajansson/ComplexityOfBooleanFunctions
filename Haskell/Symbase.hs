{-# LANGUAGE RebindableSyntax #-}
module Symbase (module Symbase, module Alg, module LevelpComplexity) where
import Alg
import LevelpComplexity
import Prelude hiding (Num(..),Fractional(..), fromIntegral, sum, product)
import DSLsofMath.PSDS
import Data.List (intersperse)

---------------SMALL TESTS-------------------------------

localtestf1 :: Ring a => a -> a
localtestf1 p = 2*p^+0*(1-p)^+2 + 2*p^+1*(1-p)^+1 - 2*p^+2*(1-p)^+0

testProbMajSymbase :: Ring a => SymBase a
--testProbMajSymbase = poly2symbase 2 testProbMaj
testProbMajSymbase = P [2,6,2]

localtestf2 :: Ring a => a -> a
localtestf2 = evalSym 2 testProbMajSymbase

localcheck :: Bool
localcheck = eqPoly (localtestf1 xP) (localtestf2 (xP :: Poly Int))

----------------SYMBASE IMPLEMENTATION------------------

symbase :: Ring a => Int -> Int -> a -> a
symbase n i = \p -> p^+i*(1-p)^+(n-i)

evalSym :: Ring a => Int -> SymBase a -> (a -> a)
evalSym n (P bs) = evalSL n bs

evalSL :: Ring a => Int -> [a] -> (a -> a)
evalSL n bs = sum (zipWith scaleF bs (map (symbase n) [0..n]))

scaleF :: Multiplicative a => a -> (x->a) -> (x->a)
scaleF c f = (c*).f

type SymBase a = Poly a
poly2symbase :: Ring a => Int -> Poly a -> SymBase a
poly2symbase n p = case caseP p of
  (a0, Nothing) -> part1
  (a0, Just q)  -> part1 + xP * poly2symbase (n-1) q
  where  (a0, mq) = caseP p
         part1 = scaleP a0 (pascalTriangle n)

caseP :: Additive a => Poly a -> (a, Maybe (Poly a))
caseP (P [])         = (zero, Nothing)
caseP (P [a0])       = (a0, Nothing)
caseP (P (a0:rest))  = (a0, Just (P rest))
  
printSymbase :: Poly Int -> String 
printSymbase (P as) = concat (intersperse "+" [show (as!!i) ++
                                               "p^" ++ show i ++
                                               "(1-p)^" ++ show (length as - 1 - i)
                                              | i <- [0..(length as-1)]
                                              ])

pascalTriangle 0 = P [1]
pascalTriangle n = smaller * P [one, one]
  where smaller = pascalTriangle (n-1)

{-
  poly2symbase n p
= -- assume form of p
  poly2symbase n (conP a0 + xP*q)
= -- assume H2(poly2symbase n, (+), (+))
  poly2symbase n (conP a0) + poly2symbase n (xP*q)
= {- poly2symbase n (conP 1) == pascalTriangle n -}
  scaleP a0 (pascalTriangle n) + poly2symbase n (xP*q)
= -- poly2symbase n (xP*q) == xP*(poly2symbase (n-1) q)
  scaleP a0 (pascalTriangle n) + xP*poly2symbase (n-1) q

-}

symbase2poly :: Ring a => Int -> SymBase a -> Poly a
symbase2poly n psym = evalSym n (liftP psym) xP

liftP :: Poly a -> Poly (Poly a)
liftP = mapP conP

conP :: a -> Poly a
conP c = P [c]

mapP :: (a->b) -> (Poly a -> Poly b)
mapP f (P as) = P (map f as)

-------------- SOME TESTS ------------------------
p2 :: Ring a => a -> a
p2 = evalSL 2 [0,0,1]

p1p :: Ring a => a -> a
p1p = evalSL 2 [0,1,0]

testp1 :: [Rational]
testp1 = map p1p l
l = [0,0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9,1]
-- testp2 :: [REAL]
testp2 :: [Rational]
testp2 = map p2 l

testA1 :: Ring a => SymBase a
testA1 = poly2symbase 9 (P [4,4,8,4,-56,20,68,-64,16,0])

flip1p :: Ring a => SymBase a -> SymBase a
flip1p (P as) = P (reverse as)

testA2 :: Ring a => SymBase a
testA2 = flip1p testA3
--poly2symbase 9 (P [4,5,4,2,-32,-3,44,-8,-20,8])

testA3 :: Ring a => SymBase a
testA3 = poly2symbase 9 (P [4,4,8,4,-59,19,100,-120,52,-8])

testA4 :: Ring a => SymBase a
testA4 = poly2symbase 9 (P [4,5,4,2,-35,-4,76,-64,16,0])
--the differences testA1-testA3 are interesting to check! 
{-
Examples:
-- n=1:
  -- p = p^1*(1-p)^(1-1) = evalSL 1 [0,1]
  -- 1 = (1-p)+p = p^0*(1-p)^(1-0) + p^1*(1-p)^(1-1) = evalSL 1 [1, 1]
-- n=2:
  -- p^2 = p^2*(1-p)^(2-2) = evalSL 2 [0,0,1]
  -- p^1 = evalSL 2 [0,1,1]
  -- p^0 = evalSL 2 [1,2,1]

-- Just exploring:
  evalSL [1,1,1] p
= 1*p² + 1*(p-p²) + 1*(p²-2p+1)
= (1-1+1)*p² + (1-2)*p + 1
= p² - p + 1

  evalSL [1,2,1] p
= 1*p² + 2*(p-p²) + 1*(p²-2p+1)
= 0*p² + 0*p + 1

  evalSL [0,1,1] p
= 0*p² + 1*(p-p²) + 1*(p²-2p+1)
= -p + 1

  evalSL [1,1,0] p
= evalSL [1-0,2-1,1-1] p
= evalSL [1,2,1] p - evalSL [0,1,1] p
= 1 - (-p+1)
= p


Attempting the general case:

assume
  f n = poly2symbase n :: Poly a -> SymBase a
specified by
  evalSym n (f n p) == evalP p
does the right thing.
What can we say about f (n+1)?

f n is a linear transformation from Poly a to SymBase a Thus it can be
fully described by its action on the base vectors (which evaluate to
symbase n i).

How is symbase (n+1) related to symbase n?

  symbase (n+1) (i+1)
= -- def. symbase
  \p -> p^+(i+1)*(1-p)^+((n+1)-(i+1))
= -- algebra
  \p -> p*p^+i*(1-p)^+(n-i)
= -- Def. (*) for functions
  id * (\p -> p^+i*(1-p)^+(n-i))
= -- def. symbase
  id * symbase n i

Not quite what we need - we need a linear combination of some symbase
n for different i with constant coefficients.

  symbase (n+1) 0
= -- def. symbase
  \p -> p^+0*(1-p)^+((n+1)-0)
= -- algebra
  \p -> (1-p)*p^+0*(1-p)^+(n-0)
= -- Def. (*) for functions
  (\p->1-p)*(\p -> p^+0*(1-p)^+(n-0))
= -- def. symbase
  (\p->1-p) * symbase n 0

Same here: not quite what we need.



let g n i = f n (e i) -- a vector in SymBase a

Calculate:
  evalSym (n+1) (g (n+1) (i+1))
= -- def. g
  evalSym (n+1) (f (n+1) (e (i+1)))
= -- spec. f
  evalP (e (i+1))
= -- def. evalP
  \p -> p^+(i+1)
= -- algebra
  \p -> p*p^+i
= -- def. (*) for functions
 id * (\p -> p^+i)
= -- def. evalP
 id * (evalP (e i))
= -- spec. f
 id * (evalSym n (f n (e i)))
= -- def. g
 id * (evalSym n (g n i))

Now, how do I push (id*) inside evalSym?

Experiments:
symbase 2 0 xP  ==  P [1,-2, 1]
symbase 2 1 xP  ==  P [0, 1,-1]
symbase 2 2 xP  ==  P [0, 0, 1]

symbase 3 0 xP  ==  P [1,-3, 3,-1]
symbase 3 1 xP  ==  P [0, 1,-2, 1]
symbase 3 2 xP  ==  P [0, 0, 1,-1]
symbase 3 3 xP  ==  P [0, 0, 0, 1]

symbase 4 0 xP  ==  P [1,-4, 6,-4, 1]
symbase 4 1 xP  ==  P [0, 1,-3, 3,-1]
symbase 4 2 xP  ==  P [0, 0, 1,-2, 1]
symbase 4 3 xP  ==  P [0, 0, 0, 1,-1]
symbase 4 4 xP  ==  P [0, 0, 0, 0, 1]


Desired properties:

  specSymbase1
  specSymbase2
  specSymbaseStep
-}
type Size = Int

specSymbaseStep :: (Eq a, Ring a) => Size -> Index -> a -> Bool
specSymbaseStep n i p = 
      symbase (n+1) (i+1) p == scaleF p     (symbase n i) p
  &&  symbase (n+1) 0 p     == scaleF (1-p) (symbase n 0) p

specSymbase1 :: (Eq a, Ring a) => Size -> Poly a -> a -> Bool
specSymbase1 n p x =  evalSym n (poly2symbase n p) x == evalP p x

specSymbase2 ::  (Eq a, Ring a) => Size -> Poly a -> Bool
specSymbase2 n po = eqPoly po (symbase2poly n (poly2symbase n po))

--notes:
{-
*Symbase> poly2symbase 9 (P [3,3,3,-3,-3,-3,1,1,1])
P [3,30,135,354,588,630,424,166,33,3]
*Symbase> poly2symbase 8 (P [3,3,3,-3,-3,-3,1,1,1])
P [3,27,108,246,342,288,136,30,3]
-}