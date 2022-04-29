{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
module GenAlg where
import Prelude (
  Read, read, ReadS, String, Char, print, putStr, ($), concat,
  Eq((==)), Ord(compare), (>), (<), Ordering,
  Maybe(Nothing, Just),
  Show, show,
  Functor(fmap),
  Foldable,
  Bool(False, True), (&&), (||), not, otherwise, and, or,
  Int, divMod, div, Integral, pred,
  Double, Rational, fst, snd,
  (.), id, const, error, asTypeOf,
  head, all, concatMap, map, (!!), (++), length, tail, zip,
  splitAt, span, drop, take, foldr, filter, zipWith, reverse,
  return, (>>=))
import Types
import Examples (maj, algmaj, alggraph45, andn, fAC, askorder, maj2)
import FiniteEnum
--I commented this import out since it caused problems for me, dont know why, but maybe it is needed
--import Haskell.DSLsofMath.DerAll.Test (test')
import Data.List (permutations, nub, (\\), intersperse, sort)
import DSLsofMath.PSDS
import Symbase
import qualified Data.List
import Data.Function (on)

{-
Specification:
Given a boolean function f, generate all(?) proper algorithms for that function.

Step 0: Brute force generation of all elements of type Alg n
  filter for "properAlg"

Step 1: Given a function, generate all proper alg. for that function
directly.
-}

{-
instance Fin (Alg 0) where univ = univAlg0
-}
univAlg0 :: [Alg 0]
univAlg0 = map Res univ


-- instance KnownNat n => Fin (Alg n) where univ = univAlg
-- univAlg = error "TODO"

univAlgStep :: KnownNat n => Int -> [Alg n] -> [Alg (S n)]
univAlgStep nN as = map Res univ ++ univAlgPick nN as

univAlgPick :: KnownNat n => Int -> [Alg n] -> [Alg (S n)]
univAlgPick nN as = do aF <- as
                       aT <- as
                       i <- [1..nN+1]
                       return (Pick i aF aT)
-- TODO don't generate duplicate "pick"
{-
When generating, the subtrees are not allowed to use the same index as
the top level Pick. One way to ensure this is to compute the set of
all indices used and only "pick" among the remaining. One has to be a
bit careful thinking about the meaning of "local" indices w.r.t global
indices. But this "brute-force" method is never going to be very
useful anyway, so it is time to go to the next level: only generate
alg. for a particular function.
-}

univAlg1 = univAlgStep 0 univAlg0
univAlg2 = univAlgStep 1 univAlg1
univAlg3 = univAlgStep 2 univAlg2


bruteforce = filter (\alg -> properAlg maj alg) univAlg3

----------------

genAlg0 :: GenT 0
genAlg0 f = [Res (f (T []))]
genAlg1 :: GenT 1
genAlg1 = genPropAlg genAlg0
genAlg2 :: GenT 2
genAlg2 = genPropAlg genAlg1
genAlg3 :: GenT 3
genAlg3 = genPropAlg genAlg2
genAlg4 :: GenT 4
genAlg4 = genPropAlg genAlg3
genAlg5 :: GenT 5
genAlg5 = genPropAlg genAlg4
genAlg6 :: GenT 6
genAlg6 = genPropAlg genAlg5
genAlg7 :: GenT 7
genAlg7 = genPropAlg genAlg6
genAlg8 :: GenT 8
genAlg8 = genPropAlg genAlg7
genAlg9 :: GenT 9
genAlg9 = genPropAlg genAlg8

genPropAlg :: (KnownNat n, KnownNat (S n)) => GenT n -> GenT (S n)
genPropAlg gP fun = case checkConst nN fun of
                 Just bs  -> map Res bs
                 Nothing  -> genPick gP diffInd fun
  where nN = fromIntegral (natVal (typeHelpFun fun))
--        diffInd = [1..nN] -- old definition
        diffInd = findDiffSubfunctions nN fun


-- whiteLie :: Alg (S n) -> Alg n
-- whiteLie = Prelude.coerce

type GenT n = BoolFun n -> [Alg n]

genPick :: KnownNat n => GenT n -> [Index] -> GenT (S n)
genPick gP is fn = do i <- is -- ++ [error ("genPick is="++show is)]
                      aF <- gP (insBit i f fn)
                      aT <- gP (insBit i t fn)
                      return (Pick i aF aT)
{-
genPick :: KnownNat n => [Index] -> GenT (S n)
genPick is fn = do i <- is
                   aF <- genPropAlg (insBit i f fn)
                   aT <- genPropAlg (insBit i t fn)
                   return (Pick i aF aT)
-}

checkConst :: KnownNat n => Int -> BoolFun n -> Maybe [Bool]
checkConst n f | isConst f  = Just [head (map f univ)]
               | otherwise  = Nothing

-- Even n=0 works: an empty tuple is basically () and f : BoolFun 0 is
-- basically a Boolean. All such functions are constant.

isZ n = fromIntegral n == (0::Int)


typeHelpFun :: BoolFun n -> Proxy n
typeHelpFun _ = Proxy

findDiffSubfunctions :: KnownNat n => Int -> BoolFun (S n) -> [Index]
findDiffSubfunctions n fun = uniqueInd
  where  try i = (i, (insBit i f fun, insBit i t fun))
         allSubFuns = map try [1..n]
         uniqueSubFuns = Data.List.nubBy ((==) `on` snd) allSubFuns
         uniqueInd = map fst uniqueSubFuns


{-
maj (T bs) =  count bs > (length bs) `div` 2
insert i' b (T t) = T (take i t ++ b : drop i t)
  where i = i'-1
insBit i b f = f . insert i b

try 1 maj = (1, (insBit 1 f maj, insBit 1 t maj)) = (1, (maj . insert 1 f, maj . insert 1 t)) = (1, (any1, any0))

allSubFuns = map try [1..n] = [(1, (any1, any0)),(2, (any1, any0)),(3, (any1, any0))]
uniqueSubFuns = Data.List.nubBy ((==) `on` snd) allSubFuns = [(1, (any1, any0))]
uniqueInd = map fst uniqueSubFuns = 1
-}

-- All algorithms for all 1-bit functions:
all1 = map genAlg1 univ
-- [ [f]              -- const False
-- , [[f<-1->t]]      -- alg. for id
-- , [[t<-1->f]]      -- alg. for not
-- , [t]              -- const True
-- ]

all2 = map genAlg2 univ
all2lens = map length all2
-- [1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1]
check2 = concatMap (\algs -> map (\alg -> properAlg (fFromAlg alg) alg) algs) all2
{-
λ> Prelude.mapM_ print all2
[f]
[[f<-1->[f<-2->t]],[f<-2->[f<-1->t]]]
[[[f<-2->t]<-1->f],[f<-2->[t<-1->f]]]
[[[f<-2->t]<-1->[f<-2->t]],[f<-2->t]]
[[f<-1->[t<-2->f]],[[f<-1->t]<-2->f]]
[[f<-1->t],[[f<-1->t]<-2->[f<-1->t]]]
[[[f<-2->t]<-1->[t<-2->f]],[[f<-1->t]<-2->[t<-1->f]]]
[[[f<-2->t]<-1->t],[[f<-1->t]<-2->t]]
[[[t<-2->f]<-1->f],[[t<-1->f]<-2->f]]
[[[t<-2->f]<-1->[f<-2->t]],[[t<-1->f]<-2->[f<-1->t]]]
[[t<-1->f],[[t<-1->f]<-2->[t<-1->f]]]
[[t<-1->[f<-2->t]],[[t<-1->f]<-2->t]]
[[[t<-2->f]<-1->[t<-2->f]],[t<-2->f]]
[[[t<-2->f]<-1->t],[t<-2->[f<-1->t]]]
[[t<-1->[t<-2->f]],[t<-2->[t<-1->f]]]
[t]
-}

-- name the first few for testing
[a0]:(a1:_):(a2a:a2b:_):_ = all2


----------------

all3 = map genAlg3 univ
all3lens = map length all3
-- 256 functions, 2696 algorithms => 10.5 alg/function
-- Improved: 1440 algs => 5.6 alg/function
all4 = map genAlg4 univ
all4lens = map length all4
all4total = sum all4lens
-- 2^(2^4) = 2^16 = 65536 functions - seem to have around 400 alg. each
-- all4total = 29073658, average = 443.6 alg. each.

--

--Some things with permutations, can this be used somehow?
testPerm :: Bool
testPerm = all (maj . T) (permutations [t,f,t])

permT :: Tuple n -> [Tuple n]
permT (T bs) = map T (nub (permutations bs))

uniqueMajTups :: [Tuple 3]
uniqueMajTups = helper ts
  where ts :: [Tuple 3]
        ts = univ

helper :: [Tuple 3] -> [Tuple 3]
helper [] = []
helper (t:ts) = t : helper ts'
  where ts' =  ts \\ ps
        ps = [p | p <- permT t, maj p == maj t]

allmaj :: [Alg 3]
allmaj = genAlg3 maj
{- 12 algoritmer (någon bug i show3 => ser ut som upprepade index). Jag tror alla kan genereras från permutationer: 3! * 2! * 1! = 12. För maj :: BoolFun 4 blir det 4! * 3! * 2! * 1! = 288 versioner (som alla är i samma ekvivalensklass).
λ> Prelude.mapM_ print allmaj
local: [[f<-1->[f<-1->t]]<-1->[[f<-1->t]<-1->t]]
local: [[f<-1->[f<-1->t]]<-1->[[f<-1->t]<-2->t]]
local: [[f<-2->[f<-1->t]]<-1->[[f<-1->t]<-1->t]]
local: [[f<-2->[f<-1->t]]<-1->[[f<-1->t]<-2->t]]
local: [[f<-1->[f<-1->t]]<-2->[[f<-1->t]<-1->t]]
local: [[f<-1->[f<-1->t]]<-2->[[f<-1->t]<-2->t]]
local: [[f<-2->[f<-1->t]]<-2->[[f<-1->t]<-1->t]]
local: [[f<-2->[f<-1->t]]<-2->[[f<-1->t]<-2->t]]
local: [[f<-1->[f<-1->t]]<-3->[[f<-1->t]<-1->t]]
local: [[f<-1->[f<-1->t]]<-3->[[f<-1->t]<-2->t]]
local: [[f<-2->[f<-1->t]]<-3->[[f<-1->t]<-1->t]]
local: [[f<-2->[f<-1->t]]<-3->[[f<-1->t]<-2->t]]
-- buggy show
global: [[f<-2->[f<-2->t]]<-1->[[f<-2->t]<-2->t]]
global: [[f<-2->[f<-2->t]]<-1->[[f<-2->t]<-3->t]]
global: [[f<-3->[f<-2->t]]<-1->[[f<-2->t]<-2->t]]
global: [[f<-3->[f<-2->t]]<-1->[[f<-2->t]<-3->t]]
global: [[f<-1->[f<-2->t]]<-2->[[f<-2->t]<-1->t]]
global: [[f<-1->[f<-2->t]]<-2->[[f<-1->t]<-3->t]]
global: [[f<-3->[f<-1->t]]<-2->[[f<-2->t]<-1->t]]
global: [[f<-3->[f<-1->t]]<-2->[[f<-1->t]<-3->t]]
global: [[f<-1->[f<-2->t]]<-3->[[f<-2->t]<-1->t]]
global: [[f<-1->[f<-2->t]]<-3->[[f<-1->t]<-2->t]]
global: [[f<-2->[f<-1->t]]<-3->[[f<-2->t]<-1->t]]
global: [[f<-2->[f<-1->t]]<-3->[[f<-1->t]<-2->t]]
-}

testall = take 3 (genAlg4 andn)
{- some examples, really unbalanced tree, but that is the nature of the all-function
[local: [f<-1->[f<-1->[f<-1->[f<-1->t]]]],
local: [f<-1->[f<-1->[f<-2->[f<-1->t]]]],
local: [f<-1->[f<-2->[f<-1->[f<-1->t]]]]]
-}


algsIterMaj :: [Alg 9]
algsIterMaj = genAlg9 maj2
psIterMaj :: Ring a => [Poly a]
psIterMaj = map alg2Poly algsIterMaj
nsIterMaj :: [Poly Int]
nsIterMaj = nub psIterMaj
symsIterMaj :: [SymBase Int]
symsIterMaj = map (poly2symbase 9) nsIterMaj

--Wanted to sort out the ones with low cost to compare if they have lower than mine, 
--to fulfill that they should at least start with 4 and not 5
--Unfortunately it takes a long time to evaluate
smallCosts :: [SymBase Int]
smallCosts = filter (\(P ps) -> head ps < 5) symsIterMaj

graphalgs :: [Alg 5]
graphalgs = genAlg5 (fFromAlg alggraph45)
testgraph45 :: [Alg 5]
testgraph45 = take 10 graphalgs
ps :: Ring a => [Poly a]
ps = map alg2Poly graphalgs
ns :: [Poly Int]
ns = nub ps

printPolyList :: [Poly Int] -> String
printPolyList ps = concat ["P" ++ show i ++"[p_]=" ++ printPoly (ps!!i) | i <- [0..length ps - 1]]
{- Don't really understand this algorithm
[local: [[f<-1->[[f<-1->[f<-1->t]]<-1->[[f<-1->t]<-1->t]]]<-1->[[[f<-1->[f<-1->t]]<-1->[[f<-1->t]<-1->t]]<-1->[[f<-1->t]<-1->t]]],
local: [[f<-1->[[f<-1->[f<-1->t]]<-1->[[f<-1->t]<-1->t]]]<-1->[[[f<-1->[f<-1->t]]<-1->[[f<-1->t]<-1->t]]<-1->[[[f<-1->t]<-2->[f<-1->t]]<-1->t]]],
local: [[f<-1->[[f<-1->[f<-1->t]]<-1->[[f<-1->t]<-1->t]]]<-1->[[[f<-1->[f<-1->t]]<-1->[[f<-1->t]<-1->t]]<-1->[[f<-1->t]<-2->t]]]]
13 unique polynomials!!
[P [2,4,2,-9,4,0],P [2,4,3,-10,4,0],P [2,4,3,-9,4,0],P [2,3,4,-10,4,0],P [3,2,3,-9,4,0],
P [3,2,4,-10,4,0],P [3,2,4,-9,4,0],P [3,1,5,-10,4,0],P [3,3,1,-8,4,0],P [3,3,2,-9,4,0],
P [3,3,2,-8,4,0],P [3,3,3,-10,4,0],P [3,3,3,-9,4,0]]
-}

algsAC :: [Alg 5]
algsAC = genAlg5 fAC
psAC :: [Poly Int]
psAC = map alg2Poly algsAC
nsAC :: [Poly Int]
nsAC = nub psAC
--54192 st
{- 39 unika
GenAlg> ps = map alg2Poly algsAC
*GenAlg> nub ps
[P [5,-8,8,0,0,0],P [5,-8,9,-1,0,0],P [5,-8,9,0,-2,0],P [5,-7,8,-1,0,0],P [5,-7,8,0,-2,0],
P [5,-7,9,-2,-2,0],P [5,-7,6,1,0,0],P [5,-7,7,0,0,0],P [5,-7,7,1,-2,0],P [5,-6,6,0,0,0],
P [5,-6,6,1,-2,0],P [5,-6,7,-1,-2,0],P [4,-2,-3,8,-2,0],P [4,-2,-2,7,-2,0],P [4,-2,-2,8,-4,0],
P [4,-1,-3,7,-2,0],P [4,-1,-3,8,-4,0],P [4,-1,-2,6,-4,0],P [5,-6,5,1,0,0],P [5,-5,5,0,0,0],
P [5,-5,5,1,-2,0],P [5,-5,6,-1,-2,0],P [4,-1,-4,8,-2,0],P [4,0,-4,7,-2,0],P [4,0,-4,8,-4,0],
P [4,0,-3,6,-4,0],P [3,3,-9,10,-2,0],P [3,3,-8,9,-2,0],P [3,3,-8,10,-4,0],P [3,4,-9,9,-2,0],
P [3,4,-9,10,-4,0],P [3,4,-8,8,-4,0],P [5,-5,5,-1,-2,0],P [4,0,-4,6,-4,0],P [3,4,-9,8,-4,0],
P [2,6,-10,9,-2,0],P [2,6,-10,10,-4,0],P [2,6,-9,8,-4,0],P [2,6,-10,8,-4,0]]
In symbase representation:
[P [5,17,26,26,17,5],P [5,17,27,28,18,5],P [5,17,27,29,18,4],P [5,18,30,31,19,5],
 P [5,18,30,32,19,4],P [5,18,31,33,18,3],P [5,18,28,27,17,5],P [5,18,29,29,18,5],
 P [5,18,29,30,18,4],P [5,19,32,32,19,5],P [5,19,32,33,19,4],P [5,19,33,34,18,3],
 P [4,18,29,27,17,5],P [4,18,30,29,18,5],P [4,18,30,30,18,4],P [4,19,33,32,19,5],
 P [4,19,33,33,19,4],P [4,19,34,34,18,3],P [5,19,31,30,18,5],P [5,20,35,35,20,5],
 P [5,20,35,36,20,4],P [5,20,36,37,19,3],P [4,19,32,30,18,5],P [4,20,36,35,20,5],
 P [4,20,36,36,20,4],P [4,20,37,37,19,3],P [3,18,33,31,18,5],P [3,18,34,33,19,5],
 P [3,18,34,34,19,4],P [3,19,37,36,20,5],P [3,19,37,37,20,4],P [3,19,38,38,19,3],
 P [5,20,35,34,16,2],P [4,20,36,34,16,2],P [3,19,37,35,16,2],P [2,16,34,35,20,5],
 P [2,16,34,36,20,4],P [2,16,35,37,19,3],P [2,16,34,34,16,2]]

Some ordering: first by the value at 0, then by the value at 1

39 in total = nine symmetric + 15 pairs of mirror images.

 p38=P [2,16,34,34,16,2] ** symmetric
 p37=P [2,16,35,37,19,3] * mirror p34
 p36=P [2,16,34,36,20,4] * mirror p33
 p35=P [2,16,34,35,20,5] * mirror p32

 p34=P [3,19,37,35,16,2] * mirror p37
 p31=P [3,19,38,38,19,3] ** symmetric
 p28=P [3,18,34,34,19,4] * mirror p17
 p30=P [3,19,37,37,20,4] * mirror p25
 p29=P [3,19,37,36,20,5] * mirror p21
 p26=P [3,18,33,31,18,5] * mirror p05
 p27=P [3,18,34,33,19,5] * mirror p11

 p33=P [4,20,36,34,16,2] * mirror p36
 p17=P [4,19,34,34,18,3] * mirror p28
 p25=P [4,20,37,37,19,3] * mirror p30
 p14=P [4,18,30,30,18,4] ** symmetric
 p16=P [4,19,33,33,19,4] ** symmetric
 p24=P [4,20,36,36,20,4] ** symmetric
 p12=P [4,18,29,27,17,5] * mirror p02
 p13=P [4,18,30,29,18,5] * mirror p08
 p22=P [4,19,32,30,18,5] * mirror p04
 p15=P [4,19,33,32,19,5] * mirror p10
 p23=P [4,20,36,35,20,5] * mirror p20

 p32=P [5,20,35,34,16,2] * mirror p35
 p21=P [5,20,36,37,19,3] * mirror p29
 p05=P [5,18,31,33,18,3] * mirror p26
 p11=P [5,19,33,34,18,3] * mirror p27
 p02=P [5,17,27,29,18,4] * mirror p12
 p08=P [5,18,29,30,18,4] * mirror p13
 p04=P [5,18,30,32,19,4] * mirror p22
 p10=P [5,19,32,33,19,4] * mirror p15
 p20=P [5,20,35,36,20,4] * mirror p23
 p06=P [5,18,28,27,17,5] * mirror p01
 p07=P [5,18,29,29,18,5] ** symmetric
 p03=P [5,18,30,31,19,5] * mirror p18
 p18=P [5,19,31,30,18,5] * mirror p03
 p09=P [5,19,32,32,19,5] ** symmetric
 p19=P [5,20,35,35,20,5] ** symmetric
 p00=P [5,17,26,26,17,5] ** symmetric
 p01=P [5,17,27,28,18,5] * mirror p06

----------------
Paired up:

 p38=P [2,16,34,34,16,2] ** symmetric
 p37=P [2,16,35,37,19,3] * mirror p34; p34=P [3,19,37,35,16,2] * mirror p37
 p36=P [2,16,34,36,20,4] * mirror p33; p33=P [4,20,36,34,16,2] * mirror p36
 p35=P [2,16,34,35,20,5] * mirror p32; p32=P [5,20,35,34,16,2] * mirror p35

 p31=P [3,19,38,38,19,3] ** symmetric
 p28=P [3,18,34,34,19,4] * mirror p17; p17=P [4,19,34,34,18,3] * mirror p28
 p30=P [3,19,37,37,20,4] * mirror p25; p25=P [4,20,37,37,19,3] * mirror p30
 p26=P [3,18,33,31,18,5] * mirror p05; p05=P [5,18,31,33,18,3] * mirror p26
 p27=P [3,18,34,33,19,5] * mirror p11; p11=P [5,19,33,34,18,3] * mirror p27
 p29=P [3,19,37,36,20,5] * mirror p21; p21=P [5,20,36,37,19,3] * mirror p29

 p14=P [4,18,30,30,18,4] ** symmetric
 p16=P [4,19,33,33,19,4] ** symmetric
 p24=P [4,20,36,36,20,4] ** symmetric
 p12=P [4,18,29,27,17,5] * mirror p02; p02=P [5,17,27,29,18,4] * mirror p12
 p13=P [4,18,30,29,18,5] * mirror p08; p08=P [5,18,29,30,18,4] * mirror p13
 p22=P [4,19,32,30,18,5] * mirror p04; p04=P [5,18,30,32,19,4] * mirror p22
 p15=P [4,19,33,32,19,5] * mirror p10; p10=P [5,19,32,33,19,4] * mirror p15
 p23=P [4,20,36,35,20,5] * mirror p20; p20=P [5,20,35,36,20,4] * mirror p23

 p00=P [5,17,26,26,17,5] ** symmetric
 p06=P [5,18,28,27,17,5] * mirror p01; p01=P [5,17,27,28,18,5] * mirror p06
 p07=P [5,18,29,29,18,5] ** symmetric
 p03=P [5,18,30,31,19,5] * mirror p18; p18=P [5,19,31,30,18,5] * mirror p03
 p09=P [5,19,32,32,19,5] ** symmetric
 p19=P [5,20,35,35,20,5] ** symmetric

-}

algAC :: Alg 5
algAC = askorder 1 2 (pick 3 p45 dt) dt dt (pick 3 dt p45)
  where p45 = askorder 4 5 dt df df dt

algCA :: Alg 5
algCA = askorder 4 5 dt p123 p123 dt
  where p123 = askorder 1 2 p3ft dt dt p3tf
        p3ft = pick 3 df dt
        p3tf = pick 3 dt df


algC0A0 :: Alg 5
algC0A0 = pick 4 c0stay c0switch
  where c0stay = pick 5 dt p123
        p123 = askorder 1 2 (pick 3 df dt) dt dt (pick 3 dt df)
        c0switch = pick 1 a0switch a0stay
        a0switch = pick 5 (pick 2 (pick 3 df dt) dt) dt
        a0stay = pick 2 dt (pick 3 dt (pick 5 df dt))

testAC :: Poly Int
testAC = alg2Poly algAC
--P [5,-8,8,0,0,0] it is the first one in the list!!

{-
AC -> glad mun   med max = 5 i p=0 och =1, min = 3    i p=1/2
CA -> ledsen mun med min = 2 i p=0 och =1, max = 3.25 i p=1/2
-}

main = print (all4total, length (all4lens))

-- Exploring alg.s for fAC:

apis :: [((Poly Int, Alg 5), Int)]
apis = sort (zip (map (\a->(alg2Poly a,a)) algsAC) [1..])

----------------

instance (Additive a, Ord a) => Ord (Poly a) where compare = comparePoly

comparePoly :: Ord a => Poly a -> Poly a -> Ordering
comparePoly (P p) (P q) = compare p q

{-
All 52=6*6+4*4 "equiv. class representatives" including 13 pairs with identical polynomial => 39 distinct polynomials.
  (Those 39 are in turn 9 symmetric + 2*15 mirror images.)
λ> Prelude.mapM_ print apis
 ((P [2, 6,-10, 8,-4,0],global: [[t<-5->[[[f<-3->t]<-2->t]<-1->[t<-2->[t<-3->f]]]]<-4->[[[[f<-3->t]<-2->t]<-1->[t<-2->[t<-3->f]]]<-5->t]]),52)
 ((P [2, 6,-10, 9,-2,0],global: [[t<-5->[[[f<-3->t]<-2->t]<-1->[t<-2->[t<-3->f]]]]<-4->[[[[f<-4->t]<-3->t]<-2->t]<-1->[t<-2->[t<-3->[f<-4->t]]]]]),49)
 ((P [2, 6,-10,10,-4,0],global: [[t<-5->[[[f<-3->t]<-2->t]<-1->[t<-2->[t<-3->f]]]]<-4->[[[[f<-4->t]<-3->t]<-2->t]<-1->[t<-2->[[t<-4->f]<-4->t]]]]),50)
 ((P [2, 6, -9, 8,-4,0],global: [[t<-5->[[[f<-3->t]<-2->t]<-1->[t<-2->[t<-3->f]]]]<-4->[[[[f<-4->t]<-3->t]<-2->t]<-1->[[t<-2->[t<-3->f]]<-4->t]]]),51)
 ((P [3, 3, -9,10,-2,0],global: [[[t<-5->[[f<-3->t]<-2->t]]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[t<-2->[t<-3->[[t<-5->f]<-4->[f<-5->t]]]]]),31)
 ((P [3, 3, -8, 9,-2,0],global: [[[t<-5->[[f<-3->t]<-2->t]]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[t<-2->[[t<-4->[t<-5->f]]<-4->[t<-4->[f<-5->t]]]]]),32)
 ((P [3, 3, -8,10,-4,0],global: [[[t<-5->[[f<-3->t]<-2->t]]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[t<-2->[[t<-4->[t<-5->f]]<-4->[[t<-5->f]<-5->t]]]]),33)
 ((P [3, 4, -9, 8,-4,0],global: [[[t<-4->[[f<-3->t]<-2->t]]<-1->[t<-2->[t<-3->[t<-4->f]]]]<-4->[[[[f<-3->t]<-2->t]<-1->[t<-2->[t<-3->f]]]<-5->t]]),48)
a((P [3, 4, -9, 9,-2,0],global: [[[t<-5->[[f<-3->t]<-2->t]]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[t<-2->[t<-3->[f<-4->t]]]]]),34)
a((P [3, 4, -9, 9,-2,0],global: [[[t<-4->[[f<-3->t]<-2->t]]<-1->[t<-2->[t<-3->[t<-4->f]]]]<-4->[[[[f<-4->t]<-3->t]<-2->t]<-1->[t<-2->[t<-3->[f<-4->t]]]]]),45)
b((P [3, 4, -9,10,-4,0],global: [[[t<-5->[[f<-3->t]<-2->t]]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[t<-2->[[t<-4->f]<-5->t]]]]),35)
b((P [3, 4, -9,10,-4,0],global: [[[t<-4->[[f<-3->t]<-2->t]]<-1->[t<-2->[t<-3->[t<-4->f]]]]<-4->[[[[f<-4->t]<-3->t]<-2->t]<-1->[t<-2->[[t<-4->f]<-4->t]]]]),46)
c((P [3, 4, -8, 8,-4,0],global: [[[t<-5->[[f<-3->t]<-2->t]]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[[t<-2->[t<-3->f]]<-5->t]]]),36)
c((P [3, 4, -8, 8,-4,0],global: [[[t<-4->[[f<-3->t]<-2->t]]<-1->[t<-2->[t<-3->[t<-4->f]]]]<-4->[[[[f<-4->t]<-3->t]<-2->t]<-1->[[t<-2->[t<-3->f]]<-4->t]]]),47)
 ((P [4,-2, -3, 8,-2,0],global: [[[[t<-5->[f<-5->t]]<-4->[[f<-5->t]<-4->t]]<-2->t]<-1->[t<-2->[t<-3->[[t<-5->f]<-4->[f<-5->t]]]]]),13)
 ((P [4,-2, -2, 7,-2,0],global: [[[[t<-5->[f<-5->t]]<-4->[[f<-5->t]<-4->t]]<-2->t]<-1->[t<-2->[[t<-4->[t<-5->f]]<-4->[t<-4->[f<-5->t]]]]]),14)
 ((P [4,-2, -2, 8,-4,0],global: [[[[t<-5->[f<-5->t]]<-4->[[f<-5->t]<-4->t]]<-2->t]<-1->[t<-2->[[t<-4->[t<-5->f]]<-4->[[t<-5->f]<-5->t]]]]),15)
 ((P [4,-1, -4, 8,-2,0],global: [[[[t<-5->[f<-4->t]]<-2->t]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[t<-2->[t<-3->[[t<-5->f]<-4->[f<-5->t]]]]]),25)
d((P [4,-1, -3, 7,-2,0],global: [[[[t<-5->[f<-5->t]]<-4->[[f<-5->t]<-4->t]]<-2->t]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[t<-2->[t<-3->[f<-4->t]]]]]),16)
d((P [4,-1, -3, 7,-2,0],global: [[[[t<-5->[f<-4->t]]<-2->t]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[t<-2->[[t<-4->[t<-5->f]]<-4->[t<-4->[f<-5->t]]]]]),26)
e((P [4,-1, -3, 8,-4,0],global: [[[[t<-5->[f<-5->t]]<-4->[[f<-5->t]<-4->t]]<-2->t]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[t<-2->[[t<-4->f]<-5->t]]]]),17)
e((P [4,-1, -3, 8,-4,0],global: [[[[t<-5->[f<-4->t]]<-2->t]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[t<-2->[[t<-4->[t<-5->f]]<-4->[[t<-5->f]<-5->t]]]]),27)
 ((P [4,-1, -2, 6,-4,0],global: [[[[t<-5->[f<-5->t]]<-4->[[f<-5->t]<-4->t]]<-2->t]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[[t<-2->[t<-3->f]]<-5->t]]]),18)
 ((P [4, 0, -4, 6,-4,0],global: [[[[t<-4->[f<-4->t]]<-2->t]<-1->[t<-2->[t<-3->[t<-4->f]]]]<-4->[[[[f<-3->t]<-2->t]<-1->[t<-2->[t<-3->f]]]<-5->t]]),44)
f((P [4, 0, -4, 7,-2,0],global: [[[[t<-5->[f<-4->t]]<-2->t]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[t<-2->[t<-3->[f<-4->t]]]]]),28)
f((P [4, 0, -4, 7,-2,0],global: [[[[t<-4->[f<-4->t]]<-2->t]<-1->[t<-2->[t<-3->[t<-4->f]]]]<-4->[[[[f<-4->t]<-3->t]<-2->t]<-1->[t<-2->[t<-3->[f<-4->t]]]]]),41)
g((P [4, 0, -4, 8,-4,0],global: [[[[t<-5->[f<-4->t]]<-2->t]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[t<-2->[[t<-4->f]<-5->t]]]]),29)
g((P [4, 0, -4, 8,-4,0],global: [[[[t<-4->[f<-4->t]]<-2->t]<-1->[t<-2->[t<-3->[t<-4->f]]]]<-4->[[[[f<-4->t]<-3->t]<-2->t]<-1->[t<-2->[[t<-4->f]<-4->t]]]]),42)
h((P [4, 0, -3, 6,-4,0],global: [[[[t<-5->[f<-4->t]]<-2->t]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[[t<-2->[t<-3->f]]<-5->t]]]),30)
h((P [4, 0, -3, 6,-4,0],global: [[[[t<-4->[f<-4->t]]<-2->t]<-1->[t<-2->[t<-3->[t<-4->f]]]]<-4->[[[[f<-4->t]<-3->t]<-2->t]<-1->[[t<-2->[t<-3->f]]<-4->t]]]),43)
 ((P [5,-8,  8, 0, 0,0],global: [[[[[t<-5->f]<-4->[f<-5->t]]<-3->t]<-2->t]<-1->[t<-2->[t<-3->[[t<-5->f]<-4->[f<-5->t]]]]]),1)
 ((P [5,-8,  9,-1, 0,0],global: [[[[[t<-5->f]<-4->[f<-5->t]]<-3->t]<-2->t]<-1->[t<-2->[[t<-4->[t<-5->f]]<-4->[t<-4->[f<-5->t]]]]]),2)
 ((P [5,-8,  9, 0,-2,0],global: [[[[[t<-5->f]<-4->[f<-5->t]]<-3->t]<-2->t]<-1->[t<-2->[[t<-4->[t<-5->f]]<-4->[[t<-5->f]<-5->t]]]]),3)
 ((P [5,-7,  6, 1, 0,0],global: [[[[[t<-5->f]<-4->t]<-4->[[f<-5->t]<-4->t]]<-2->t]<-1->[t<-2->[t<-3->[[t<-5->f]<-4->[f<-5->t]]]]]),7)
 ((P [5,-7,  7, 0, 0,0],global: [[[[[t<-5->f]<-4->t]<-4->[[f<-5->t]<-4->t]]<-2->t]<-1->[t<-2->[[t<-4->[t<-5->f]]<-4->[t<-4->[f<-5->t]]]]]),8)
 ((P [5,-7,  7, 1,-2,0],global: [[[[[t<-5->f]<-4->t]<-4->[[f<-5->t]<-4->t]]<-2->t]<-1->[t<-2->[[t<-4->[t<-5->f]]<-4->[[t<-5->f]<-5->t]]]]),9)
 ((P [5,-7,  8,-1, 0,0],global: [[[[[t<-5->f]<-4->[f<-5->t]]<-3->t]<-2->t]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[t<-2->[t<-3->[f<-4->t]]]]]),4)
 ((P [5,-7,  8, 0,-2,0],global: [[[[[t<-5->f]<-4->[f<-5->t]]<-3->t]<-2->t]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[t<-2->[[t<-4->f]<-5->t]]]]),5)
 ((P [5,-7,  9,-2,-2,0],global: [[[[[t<-5->f]<-4->[f<-5->t]]<-3->t]<-2->t]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[[t<-2->[t<-3->f]]<-5->t]]]),6)
 ((P [5,-6,  5, 1, 0,0],global: [[[[[t<-4->f]<-3->t]<-2->t]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[t<-2->[t<-3->[[t<-5->f]<-4->[f<-5->t]]]]]),19)
i((P [5,-6,  6, 0, 0,0],global: [[[[[t<-5->f]<-4->t]<-4->[[f<-5->t]<-4->t]]<-2->t]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[t<-2->[t<-3->[f<-4->t]]]]]),10)
i((P [5,-6,  6, 0, 0,0],global: [[[[[t<-4->f]<-3->t]<-2->t]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[t<-2->[[t<-4->[t<-5->f]]<-4->[t<-4->[f<-5->t]]]]]),20)
j((P [5,-6,  6, 1,-2,0],global: [[[[[t<-5->f]<-4->t]<-4->[[f<-5->t]<-4->t]]<-2->t]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[t<-2->[[t<-4->f]<-5->t]]]]),11)
j((P [5,-6,  6, 1,-2,0],global: [[[[[t<-4->f]<-3->t]<-2->t]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[t<-2->[[t<-4->[t<-5->f]]<-4->[[t<-5->f]<-5->t]]]]),21)
 ((P [5,-6,  7,-1,-2,0],global: [[[[[t<-5->f]<-4->t]<-4->[[f<-5->t]<-4->t]]<-2->t]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[[t<-2->[t<-3->f]]<-5->t]]]),12)
 ((P [5,-5,  5,-1,-2,0],global: [[[[[t<-4->f]<-3->t]<-2->t]<-1->[t<-2->[t<-3->[t<-4->f]]]]<-4->[[[[f<-3->t]<-2->t]<-1->[t<-2->[t<-3->f]]]<-5->t]]),40)
k((P [5,-5,  5, 0, 0,0],global: [[[[[t<-4->f]<-3->t]<-2->t]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[t<-2->[t<-3->[f<-4->t]]]]]),22)
k((P [5,-5,  5, 0, 0,0],global: [[[[[t<-4->f]<-3->t]<-2->t]<-1->[t<-2->[t<-3->[t<-4->f]]]]<-4->[[[[f<-4->t]<-3->t]<-2->t]<-1->[t<-2->[t<-3->[f<-4->t]]]]]),37)
l((P [5,-5,  5, 1,-2,0],global: [[[[[t<-4->f]<-3->t]<-2->t]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[t<-2->[[t<-4->f]<-5->t]]]]),23)
l((P [5,-5,  5, 1,-2,0],global: [[[[[t<-4->f]<-3->t]<-2->t]<-1->[t<-2->[t<-3->[t<-4->f]]]]<-4->[[[[f<-4->t]<-3->t]<-2->t]<-1->[t<-2->[[t<-4->f]<-4->t]]]]),38)
m((P [5,-5,  6,-1,-2,0],global: [[[[[t<-4->f]<-3->t]<-2->t]<-4->[[[f<-4->t]<-3->t]<-2->t]]<-1->[[t<-2->[t<-3->[t<-4->f]]]<-4->[[t<-2->[t<-3->f]]<-5->t]]]),24)
m((P [5,-5,  6,-1,-2,0],global: [[[[[t<-4->f]<-3->t]<-2->t]<-1->[t<-2->[t<-3->[t<-4->f]]]]<-4->[[[[f<-4->t]<-3->t]<-2->t]<-1->[[t<-2->[t<-3->f]]<-4->t]]]),39)

-}
