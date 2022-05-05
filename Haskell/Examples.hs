{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
module Examples where
import Prelude (
  Read, read, ReadS, String, Char, print,
  Eq((==)), (>), (<),
  Maybe(Nothing, Just),
  Show, show,
  Functor(fmap),
  Foldable,
  Bool(False, True), (&&), (||), not, otherwise, and, or,
  Int, divMod, div, Integral, pred,
  Double, Rational,
  (.), id, const, error, asTypeOf, snd,
  head, all, concatMap, map, (!!), (++), length, tail,
  splitAt, span, drop, take, foldr, filter, zipWith, reverse)
import Types
import FiniteEnum
import Symbase
import Data.Function(on)
import Data.List(nub, nubBy)

---------------- ALGORITHM EXAMPLES ----------------
-- All algorithms for the and_2 function:
alg1, alg2 :: Alg Two
alg1 = pick 1 (Res f) (pick 2 (Res f) (Res t))
alg2 = pick 2 (Res f) (pick 1 (Res f) (Res t))

testalg1 = cost alg1 (T [t,t])

flip:: Alg n -> Alg n
-- flip Done = Done
flip (Res b) = Res b
flip (Pick i a0 a1) = Pick i (flip a1) (flip a0)

alg3flip :: Alg Three
alg3flip = pick 3 alg1 (flip alg2)
--it is equivalent to algmaj

testalgmaj = map (cost algmaj) (univ :: [Tuple Three])
algmaj :: Alg Three
algmaj = pick 1 (pick 2 (Res f)  -- 1=f,2=f -> false indep. of 3
                        pick3ft)
                (pick 2 pick3ft
                        (Res t)) -- 1=t,2=t -> true indep. of 3
  where pick3ft = pick 3 (Res f) (Res t)

---------------- ANDN EXAMPLE ----------------
{-
andn is a good example because it is one of the first to compute
complexity for.  Also because the set of algorithms for and has a very
simple structure - the are all "right-leaning" trees. Thus an
  a :: Alg n andn
is basically just a list of picked indices.
-}
andn :: Tuple n -> Bool
andn (T bs) = and bs

testf1 :: BoolFun Two
testf1 = insBit 1 True andn  -- same as andn :: BoolFun 2

showTest1 :: String
showTest1 = show testf1

testf1TF :: Bool
testf1TF = testf1 tf

-----------------------------------fun AC------------------------------

fAC :: Tuple 5 -> Bool 
fAC (T bs) = not (same as) || same cs
  where as = take 3 bs 
        cs = take 2 (drop 3 bs)

same :: [Bool] -> Bool 
same bs = and bs || not (or bs)

---------------- TUP HELP FUNCTIONS FOR ITERATED MAJORITY ----------------
concTup :: Tup n (Tup m a) -> Tup (Mul n m) a
concTup (T ts) = T (concatMap unT ts)

type BlockSize = Int
chunkList :: BlockSize -> [a] -> [[a]]
chunkList n [] = []
chunkList n xs | length xs < n = [xs]  -- or give an error "not matching shape"
chunkList n xs = case splitAt n xs of
  (xs, rest) -> xs : chunkList n rest

splitTup :: BlockSize -> Tup (Mul n m) a -> Tup n (Tup m a)
splitTup m (T bs) = T (map T (chunkList m bs))

majmaj :: Tup n (Tuple m) -> Bool
majmaj = maj . fmap maj

-- gerrymandering
testinp1, testinp2 :: Tup Three (Tuple Three)
testinp1 = T [tff, ftf, tft] -- minority loses
-- after swapping (1,3) with (2,2)
testinp2 = T [tft, fff, tft] -- minority wins

test1, test2 :: Bool
test1 = majmaj testinp1
test2 = majmaj testinp2

testenum :: [Tup Three (Tuple Three)]
testenum = univ

testenumfun :: [BoolFun Two]
testenumfun = univ

---------------- ITERATED MAJORITY ----------------
-- maj2 :: Tup Nine Bool -> Bool
maj2 :: Tup (Mul Three Three) Bool -> Bool
maj2 as = maj (fmap maj (splitTup3 as))

splitTup3 :: Tup Nine a -> Tup Three (Tup Three a)
splitTup3 = splitTup 3
-- splitTup3 (T bs) = T (map T (chunkList 3 bs))

concTup3 :: Tup Three (Tup Three a) -> Tup Nine a
concTup3 = concTup
-- concTup3 (T ts) = T (concatMap unT ts)

ninetups = univ :: [Tuple Nine]
firsttup = head ninetups
T firstlist = firsttup


maj :: Tuple n -> Bool
maj (T bs) =  count bs > (length bs) `div` 2

splitTup32 :: Tup 6 a -> Tup 2 (Tup 3 a)
splitTup32 = splitTup 3

and2maj :: Tuple 6 -> Bool
and2maj = andn . fmap maj . splitTup32

count :: [Bool] -> Int
count [] = 0
count (b:bs) | b         = 1 + count bs
             | otherwise = count bs

testf2 :: BoolFun Two
testf2 = insBit 1 True maj  -- or2

testf2TF :: Bool
testf2TF = testf2 tf

-- Example of an improper algorithm

alg3 :: Alg 3
alg3 = pick 3 alg1 alg2

testImproper :: Bool
testImproper = not (properAlg andn alg3)

{-
testProb3 :: Poly Int
testProb3 = expectation alg3
-- Res  ult: 2+p

-}

algmajgen i     j       k
          ai0j0 ai0j1k0 ai0j1k1
          ai1j0k0 ai1j0k1 ai1j1
        = pick i (pick j ai0j0 (pick k ai0j1k0 ai0j1k1))
                 (pick j (pick k ai1j0k0 ai1j0k1) ai1j1)

askorder :: (KnownNat (S n), KnownNat n) =>
     Index -> Index ->
     Alg n -> Alg n -> Alg n -> Alg n ->
     Alg (S (S n))
askorder i j t00 t01 t10 t11 = pick i (pick j t00 t01) (pick j t10 t11)

--------------------------------------------ALGORITHMS FOR GRAPHS------------------------------------------------------

graph45 :: Tuple 5 -> Bool
graph45 = fFromAlg alggraph45 -- has 14 True - correct? yes it seems correct

--Graph connectivity example algorithm, starting with 1
--Correct, updated calculations now
alggraph45 :: Alg 5
alggraph45 = pick 1 alggraph44class2 reduced45graph

--Found the error in my calculations, should now be correct!!
reduced45graph :: Alg 4
reduced45graph = askorder 3 4 df p25 p25 dt

p25 :: Alg 2
p25 = pick 2 (pick 5 df dt) dt

--This expecation is correct P [1,2,2,-2,0]
alggraph44class2 :: Alg 4
alggraph44class2 = pick 2 df alg345

alg345 :: Alg 3
alg345 = algmajgen 3 4 5 df df dt df dt dt

--now the one starting with 5, also not correct, check the calculations
alggraph45start5 :: Alg 5
alggraph45start5 = pick 5 alggraph44class1 reduced45graph2

--now correct expectation, wrote it in wrong first
alggraph44class1 :: Alg 4
alggraph44class1 = askorder 1 2 df p34 p34 p34'
  where p34 = pick 3 df (pick 4 df dt)
        p34' = pick 3 (pick 4 df dt) dt

--also correct
reduced45graph2 :: Alg 4
reduced45graph2 = pick 1 (pick 2 df p34) p34'
  where p34 :: Alg 2
        p34 = pick 3 (pick 4 df dt) dt
        p34' :: Alg 3
        p34' = pick 3 (pick 4 df dt) dt


---------------------------------------------ALGORITHMS FOR ITERATED MAJORITY-----------------------------------------------------
--We write in the naive algorithm for iterated majority, it is proper, and the expectation is correct!
type KnownSix n = (KnownNat n, KnownNat (S n), KnownNat (S (S n)), KnownNat (S (S (S n))), KnownNat (S (S (S (S n)))), KnownNat (S (S (S (S (S n)))))) 

symbIterMaj :: [SymBase Int]
symbIterMaj = map (\alg -> poly2symbase 9 (alg2Poly alg)) [algitermaj, algitermaj2,algitermaj3,algitermaj4]
{-
[P [4,40,184,508,864,864,508,184,40,4],
 P [4,40,183,503,857,861,508,184,40,4],
 P [4,40,184,508,861,857,503,183,40,4], 
 P [4,40,183,503,854,854,503,183,40,4]]
-}

algitermaj:: Alg 9
algitermaj = algmajgen 1 2 3 alg456a alg456a alg456b alg456a alg456b alg456b

alg456a :: KnownSix n => Alg (S (S (S (S (S (S n))))))
alg456a = algmajgen 4 5 6 df df alg789 df alg789 alg789

alg456b :: KnownSix n => Alg (S (S (S (S (S (S n))))))
alg456b = algmajgen 4 5 6 alg789 alg789 dt alg789 dt dt

alg789 :: (KnownNat n, KnownNat (S n), KnownNat (S (S n))) => Alg (S (S (S n)))
alg789 = algmajgen 7 8 9 df df dt df dt dt

algitermaj4 :: Alg 9
algitermaj4 = algmajgen 1 2 3 d00 d010 d011 d100 d101 d11

check_algitermaj4 = properAlg maj2 algitermaj4  &&
                    fFromAlg algitermaj4 == maj2

d00 :: Alg 7
d00 = pick 4 (pick 5 df (pick 6 df algcont3789)) alg37895601

d010 :: Alg 6
d010 = pick 4 (pick 5 df (pick 6 df algcont789)) alg7895601

d011 :: Alg 6
d011 = pick 4 alg7895610 (pick 5 (pick 6 algcont789 dt) dt)

d100 :: Alg 6
d100 = d010

d101 :: Alg 6
d101 = d011

d11 :: Alg 7
d11 = pick 4 alg37895610 (pick 5 (pick 6 algcont3789 dt) dt)

alg37895601 :: Alg 6
alg37895601 = askorder 7 8 df (pick 9 df alg356) (pick 9 df alg356) alg3569

alg356 :: Alg 3
alg356 = pick 5 (pick 6 df dt) dt
alg3569 :: Alg 4
alg3569 = pick 5 (pick 6 df dt) dt

alg7895601 :: Alg 5
alg7895601 = askorder 7 8 df (pick 9 df alg56) (pick 9 df alg56) alg569

alg56 :: Alg 2
alg56 = pick 5 (pick 6 df dt) dt
alg569 :: Alg 3
alg569 = pick 5 (pick 6 df dt) dt

alg7895610 :: Alg 5
alg7895610 = askorder 7 8 alg569' (pick 9 alg56' dt) (pick 9 alg56' dt) dt

alg56' :: Alg 2
alg56' = pick 5 df (pick 6 df dt)
alg569' :: Alg 3
alg569' = pick 5 df (pick 6 df dt)

alg37895610 :: Alg 6
alg37895610 = askorder 7 8 alg3569' (pick 9 alg356' dt) (pick 9 alg356' dt) dt

alg356' :: Alg 3
alg356' = pick 5 df (pick 6 df dt)
alg3569' :: Alg 4
alg3569' = pick 5 df (pick 6 df dt)

algcont3789 :: Alg 4
algcont3789 = algmajgen 7 8 9 df df dt df dt dt
algcont6789 :: Alg 4
algcont6789 = algmajgen 7 8 9 df df dt df dt dt
algcont36789 :: Alg 5
algcont36789 = algmajgen 7 8 9 df df dt df dt dt
algcont789 :: Alg 3
algcont789 = algmajgen 7 8 9 df df dt df dt dt

algitermaj2 :: Alg 9
algitermaj2 = algmajgen 1 2 3 b00 b010 b011 b100 b101 b11

b00 :: Alg 7
b00 = d00

b010 :: Alg 6
b010 = d010

b011 :: Alg 6
b011 = algmajgen 4 5 6 algcont6789 algcont789 dt algcont789 dt dt

b100 :: Alg 6
b100 = d100

b101 :: Alg 6
b101 = b011

b11 :: Alg 7
b11 = algmajgen 4 5 6 algcont36789 algcont3789 dt algcont3789 dt dt

algitermaj3 :: Alg 9
algitermaj3 = algmajgen 1 2 3 c00 c010 c011 c100 c101 c11

c00 :: Alg 7
c00 = algmajgen 4 5 6 df df algcont3789 df algcont3789 algcont36789

c010 :: Alg 6
c010 = algmajgen 4 5 6 df df algcont789 df algcont789 algcont6789

c011 :: Alg 6
c011 = d011

c100 :: Alg 6
c100 = c010

c101 :: Alg 6
c101 = d011

c11 :: Alg 7
c11 = d11

----------------
-- Some experiments: how many different functions do we get after one pick?
-- For maj is just 1: all initial picks reduce to the exact same function
-- :set -XDataKinds
hf :: Index -> BoolFun 8
hf i = insBit i f maj2
hfs :: [BoolFun 8]
hfs  = map            hf      [1..9]
hfs' = map (\i -> (i, hf i))  [1..9]
uniqehfs = Data.List.nubBy ((==) `on` snd) hfs'
{- For maj2 we get just three different functions:
1: tab2Fun [({FFFFFFFF},False),({FFFFFFFT},False),({FFFFFFTF},False),({FFFFFFTT},False),({FFFFFTFF},False),({FFFFFTFT},False),({FFFFFTTF},False),({FFFFFTTT},False),({FFFFTFFF},False),({FFFFTFFT},False),({FFFFTFTF},False),({FFFFTFTT},False),({FFFFTTFF},False),({FFFFTTFT},False),({FFFFTTTF},False),({FFFFTTTT},False),({FFFTFFFF},False),({FFFTFFFT},False),({FFFTFFTF},False),({FFFTFFTT},False),({FFFTFTFF},False),({FFFTFTFT},False),({FFFTFTTF},False),({FFFTFTTT},False),({FFFTTFFF},False),({FFFTTFFT},False),({FFFTTFTF},False),({FFFTTFTT},True),({FFFTTTFF},False),({FFFTTTFT},True),({FFFTTTTF},True),({FFFTTTTT},True),({FFTFFFFF},False),({FFTFFFFT},False),({FFTFFFTF},False),({FFTFFFTT},False),({FFTFFTFF},False),({FFTFFTFT},False),({FFTFFTTF},False),({FFTFFTTT},False),({FFTFTFFF},False),({FFTFTFFT},False),({FFTFTFTF},False),({FFTFTFTT},True),({FFTFTTFF},False),({FFTFTTFT},True),({FFTFTTTF},True),({FFTFTTTT},True),({FFTTFFFF},False),({FFTTFFFT},False),({FFTTFFTF},False),({FFTTFFTT},True),({FFTTFTFF},False),({FFTTFTFT},True),({FFTTFTTF},True),({FFTTFTTT},True),({FFTTTFFF},False),({FFTTTFFT},False),({FFTTTFTF},False),({FFTTTFTT},True),({FFTTTTFF},False),({FFTTTTFT},True),({FFTTTTTF},True),({FFTTTTTT},True),({FTFFFFFF},False),({FTFFFFFT},False),({FTFFFFTF},False),({FTFFFFTT},False),({FTFFFTFF},False),({FTFFFTFT},False),({FTFFFTTF},False),({FTFFFTTT},False),({FTFFTFFF},False),({FTFFTFFT},False),({FTFFTFTF},False),({FTFFTFTT},False),({FTFFTTFF},False),({FTFFTTFT},False),({FTFFTTTF},False),({FTFFTTTT},False),({FTFTFFFF},False),({FTFTFFFT},False),({FTFTFFTF},False),({FTFTFFTT},False),({FTFTFTFF},False),({FTFTFTFT},False),({FTFTFTTF},False),({FTFTFTTT},False),({FTFTTFFF},False),({FTFTTFFT},False),({FTFTTFTF},False),({FTFTTFTT},True),({FTFTTTFF},False),({FTFTTTFT},True),({FTFTTTTF},True),({FTFTTTTT},True),({FTTFFFFF},False),({FTTFFFFT},False),({FTTFFFTF},False),({FTTFFFTT},False),({FTTFFTFF},False),({FTTFFTFT},False),({FTTFFTTF},False),({FTTFFTTT},False),({FTTFTFFF},False),({FTTFTFFT},False),({FTTFTFTF},False),({FTTFTFTT},True),({FTTFTTFF},False),({FTTFTTFT},True),({FTTFTTTF},True),({FTTFTTTT},True),({FTTTFFFF},False),({FTTTFFFT},False),({FTTTFFTF},False),({FTTTFFTT},True),({FTTTFTFF},False),({FTTTFTFT},True),({FTTTFTTF},True),({FTTTFTTT},True),({FTTTTFFF},False),({FTTTTFFT},False),({FTTTTFTF},False),({FTTTTFTT},True),({FTTTTTFF},False),({FTTTTTFT},True),({FTTTTTTF},True),({FTTTTTTT},True),({TFFFFFFF},False),({TFFFFFFT},False),({TFFFFFTF},False),({TFFFFFTT},False),({TFFFFTFF},False),({TFFFFTFT},False),({TFFFFTTF},False),({TFFFFTTT},False),({TFFFTFFF},False),({TFFFTFFT},False),({TFFFTFTF},False),({TFFFTFTT},False),({TFFFTTFF},False),({TFFFTTFT},False),({TFFFTTTF},False),({TFFFTTTT},False),({TFFTFFFF},False),({TFFTFFFT},False),({TFFTFFTF},False),({TFFTFFTT},False),({TFFTFTFF},False),({TFFTFTFT},False),({TFFTFTTF},False),({TFFTFTTT},False),({TFFTTFFF},False),({TFFTTFFT},False),({TFFTTFTF},False),({TFFTTFTT},True),({TFFTTTFF},False),({TFFTTTFT},True),({TFFTTTTF},True),({TFFTTTTT},True),({TFTFFFFF},False),({TFTFFFFT},False),({TFTFFFTF},False),({TFTFFFTT},False),({TFTFFTFF},False),({TFTFFTFT},False),({TFTFFTTF},False),({TFTFFTTT},False),({TFTFTFFF},False),({TFTFTFFT},False),({TFTFTFTF},False),({TFTFTFTT},True),({TFTFTTFF},False),({TFTFTTFT},True),({TFTFTTTF},True),({TFTFTTTT},True),({TFTTFFFF},False),({TFTTFFFT},False),({TFTTFFTF},False),({TFTTFFTT},True),({TFTTFTFF},False),({TFTTFTFT},True),({TFTTFTTF},True),({TFTTFTTT},True),({TFTTTFFF},False),({TFTTTFFT},False),({TFTTTFTF},False),({TFTTTFTT},True),({TFTTTTFF},False),({TFTTTTFT},True),({TFTTTTTF},True),({TFTTTTTT},True),({TTFFFFFF},False),({TTFFFFFT},False),({TTFFFFTF},False),({TTFFFFTT},True),({TTFFFTFF},False),({TTFFFTFT},True),({TTFFFTTF},True),({TTFFFTTT},True),({TTFFTFFF},False),({TTFFTFFT},False),({TTFFTFTF},False),({TTFFTFTT},True),({TTFFTTFF},False),({TTFFTTFT},True),({TTFFTTTF},True),({TTFFTTTT},True),({TTFTFFFF},False),({TTFTFFFT},False),({TTFTFFTF},False),({TTFTFFTT},True),({TTFTFTFF},False),({TTFTFTFT},True),({TTFTFTTF},True),({TTFTFTTT},True),({TTFTTFFF},True),({TTFTTFFT},True),({TTFTTFTF},True),({TTFTTFTT},True),({TTFTTTFF},True),({TTFTTTFT},True),({TTFTTTTF},True),({TTFTTTTT},True),({TTTFFFFF},False),({TTTFFFFT},False),({TTTFFFTF},False),({TTTFFFTT},True),({TTTFFTFF},False),({TTTFFTFT},True),({TTTFFTTF},True),({TTTFFTTT},True),({TTTFTFFF},True),({TTTFTFFT},True),({TTTFTFTF},True),({TTTFTFTT},True),({TTTFTTFF},True),({TTTFTTFT},True),({TTTFTTTF},True),({TTTFTTTT},True),({TTTTFFFF},True),({TTTTFFFT},True),({TTTTFFTF},True),({TTTTFFTT},True),({TTTTFTFF},True),({TTTTFTFT},True),({TTTTFTTF},True),({TTTTFTTT},True),({TTTTTFFF},True),({TTTTTFFT},True),({TTTTTFTF},True),({TTTTTFTT},True),({TTTTTTFF},True),({TTTTTTFT},True),({TTTTTTTF},True),({TTTTTTTT},True)]
4: tab2Fun [({FFFFFFFF},False),({FFFFFFFT},False),({FFFFFFTF},False),({FFFFFFTT},False),({FFFFFTFF},False),({FFFFFTFT},False),({FFFFFTTF},False),({FFFFFTTT},False),({FFFFTFFF},False),({FFFFTFFT},False),({FFFFTFTF},False),({FFFFTFTT},False),({FFFFTTFF},False),({FFFFTTFT},False),({FFFFTTTF},False),({FFFFTTTT},False),({FFFTFFFF},False),({FFFTFFFT},False),({FFFTFFTF},False),({FFFTFFTT},False),({FFFTFTFF},False),({FFFTFTFT},False),({FFFTFTTF},False),({FFFTFTTT},False),({FFFTTFFF},False),({FFFTTFFT},False),({FFFTTFTF},False),({FFFTTFTT},True),({FFFTTTFF},False),({FFFTTTFT},True),({FFFTTTTF},True),({FFFTTTTT},True),({FFTFFFFF},False),({FFTFFFFT},False),({FFTFFFTF},False),({FFTFFFTT},False),({FFTFFTFF},False),({FFTFFTFT},False),({FFTFFTTF},False),({FFTFFTTT},False),({FFTFTFFF},False),({FFTFTFFT},False),({FFTFTFTF},False),({FFTFTFTT},False),({FFTFTTFF},False),({FFTFTTFT},False),({FFTFTTTF},False),({FFTFTTTT},False),({FFTTFFFF},False),({FFTTFFFT},False),({FFTTFFTF},False),({FFTTFFTT},False),({FFTTFTFF},False),({FFTTFTFT},False),({FFTTFTTF},False),({FFTTFTTT},False),({FFTTTFFF},False),({FFTTTFFT},False),({FFTTTFTF},False),({FFTTTFTT},True),({FFTTTTFF},False),({FFTTTTFT},True),({FFTTTTTF},True),({FFTTTTTT},True),({FTFFFFFF},False),({FTFFFFFT},False),({FTFFFFTF},False),({FTFFFFTT},False),({FTFFFTFF},False),({FTFFFTFT},False),({FTFFFTTF},False),({FTFFFTTT},False),({FTFFTFFF},False),({FTFFTFFT},False),({FTFFTFTF},False),({FTFFTFTT},False),({FTFFTTFF},False),({FTFFTTFT},False),({FTFFTTTF},False),({FTFFTTTT},False),({FTFTFFFF},False),({FTFTFFFT},False),({FTFTFFTF},False),({FTFTFFTT},False),({FTFTFTFF},False),({FTFTFTFT},False),({FTFTFTTF},False),({FTFTFTTT},False),({FTFTTFFF},False),({FTFTTFFT},False),({FTFTTFTF},False),({FTFTTFTT},True),({FTFTTTFF},False),({FTFTTTFT},True),({FTFTTTTF},True),({FTFTTTTT},True),({FTTFFFFF},False),({FTTFFFFT},False),({FTTFFFTF},False),({FTTFFFTT},True),({FTTFFTFF},False),({FTTFFTFT},True),({FTTFFTTF},True),({FTTFFTTT},True),({FTTFTFFF},False),({FTTFTFFT},False),({FTTFTFTF},False),({FTTFTFTT},True),({FTTFTTFF},False),({FTTFTTFT},True),({FTTFTTTF},True),({FTTFTTTT},True),({FTTTFFFF},False),({FTTTFFFT},False),({FTTTFFTF},False),({FTTTFFTT},True),({FTTTFTFF},False),({FTTTFTFT},True),({FTTTFTTF},True),({FTTTFTTT},True),({FTTTTFFF},True),({FTTTTFFT},True),({FTTTTFTF},True),({FTTTTFTT},True),({FTTTTTFF},True),({FTTTTTFT},True),({FTTTTTTF},True),({FTTTTTTT},True),({TFFFFFFF},False),({TFFFFFFT},False),({TFFFFFTF},False),({TFFFFFTT},False),({TFFFFTFF},False),({TFFFFTFT},False),({TFFFFTTF},False),({TFFFFTTT},False),({TFFFTFFF},False),({TFFFTFFT},False),({TFFFTFTF},False),({TFFFTFTT},False),({TFFFTTFF},False),({TFFFTTFT},False),({TFFFTTTF},False),({TFFFTTTT},False),({TFFTFFFF},False),({TFFTFFFT},False),({TFFTFFTF},False),({TFFTFFTT},False),({TFFTFTFF},False),({TFFTFTFT},False),({TFFTFTTF},False),({TFFTFTTT},False),({TFFTTFFF},False),({TFFTTFFT},False),({TFFTTFTF},False),({TFFTTFTT},True),({TFFTTTFF},False),({TFFTTTFT},True),({TFFTTTTF},True),({TFFTTTTT},True),({TFTFFFFF},False),({TFTFFFFT},False),({TFTFFFTF},False),({TFTFFFTT},True),({TFTFFTFF},False),({TFTFFTFT},True),({TFTFFTTF},True),({TFTFFTTT},True),({TFTFTFFF},False),({TFTFTFFT},False),({TFTFTFTF},False),({TFTFTFTT},True),({TFTFTTFF},False),({TFTFTTFT},True),({TFTFTTTF},True),({TFTFTTTT},True),({TFTTFFFF},False),({TFTTFFFT},False),({TFTTFFTF},False),({TFTTFFTT},True),({TFTTFTFF},False),({TFTTFTFT},True),({TFTTFTTF},True),({TFTTFTTT},True),({TFTTTFFF},True),({TFTTTFFT},True),({TFTTTFTF},True),({TFTTTFTT},True),({TFTTTTFF},True),({TFTTTTFT},True),({TFTTTTTF},True),({TFTTTTTT},True),({TTFFFFFF},False),({TTFFFFFT},False),({TTFFFFTF},False),({TTFFFFTT},True),({TTFFFTFF},False),({TTFFFTFT},True),({TTFFFTTF},True),({TTFFFTTT},True),({TTFFTFFF},False),({TTFFTFFT},False),({TTFFTFTF},False),({TTFFTFTT},True),({TTFFTTFF},False),({TTFFTTFT},True),({TTFFTTTF},True),({TTFFTTTT},True),({TTFTFFFF},False),({TTFTFFFT},False),({TTFTFFTF},False),({TTFTFFTT},True),({TTFTFTFF},False),({TTFTFTFT},True),({TTFTFTTF},True),({TTFTFTTT},True),({TTFTTFFF},True),({TTFTTFFT},True),({TTFTTFTF},True),({TTFTTFTT},True),({TTFTTTFF},True),({TTFTTTFT},True),({TTFTTTTF},True),({TTFTTTTT},True),({TTTFFFFF},False),({TTTFFFFT},False),({TTTFFFTF},False),({TTTFFFTT},True),({TTTFFTFF},False),({TTTFFTFT},True),({TTTFFTTF},True),({TTTFFTTT},True),({TTTFTFFF},False),({TTTFTFFT},False),({TTTFTFTF},False),({TTTFTFTT},True),({TTTFTTFF},False),({TTTFTTFT},True),({TTTFTTTF},True),({TTTFTTTT},True),({TTTTFFFF},False),({TTTTFFFT},False),({TTTTFFTF},False),({TTTTFFTT},True),({TTTTFTFF},False),({TTTTFTFT},True),({TTTTFTTF},True),({TTTTFTTT},True),({TTTTTFFF},True),({TTTTTFFT},True),({TTTTTFTF},True),({TTTTTFTT},True),({TTTTTTFF},True),({TTTTTTFT},True),({TTTTTTTF},True),({TTTTTTTT},True)]
7: tab2Fun [({FFFFFFFF},False),({FFFFFFFT},False),({FFFFFFTF},False),({FFFFFFTT},False),({FFFFFTFF},False),({FFFFFTFT},False),({FFFFFTTF},False),({FFFFFTTT},False),({FFFFTFFF},False),({FFFFTFFT},False),({FFFFTFTF},False),({FFFFTFTT},False),({FFFFTTFF},False),({FFFFTTFT},False),({FFFFTTTF},False),({FFFFTTTT},True),({FFFTFFFF},False),({FFFTFFFT},False),({FFFTFFTF},False),({FFFTFFTT},False),({FFFTFTFF},False),({FFFTFTFT},False),({FFFTFTTF},False),({FFFTFTTT},True),({FFFTTFFF},False),({FFFTTFFT},False),({FFFTTFTF},False),({FFFTTFTT},True),({FFFTTTFF},False),({FFFTTTFT},False),({FFFTTTTF},False),({FFFTTTTT},True),({FFTFFFFF},False),({FFTFFFFT},False),({FFTFFFTF},False),({FFTFFFTT},False),({FFTFFTFF},False),({FFTFFTFT},False),({FFTFFTTF},False),({FFTFFTTT},False),({FFTFTFFF},False),({FFTFTFFT},False),({FFTFTFTF},False),({FFTFTFTT},False),({FFTFTTFF},False),({FFTFTTFT},False),({FFTFTTTF},False),({FFTFTTTT},True),({FFTTFFFF},False),({FFTTFFFT},False),({FFTTFFTF},False),({FFTTFFTT},False),({FFTTFTFF},False),({FFTTFTFT},False),({FFTTFTTF},False),({FFTTFTTT},True),({FFTTTFFF},False),({FFTTTFFT},False),({FFTTTFTF},False),({FFTTTFTT},True),({FFTTTTFF},False),({FFTTTTFT},False),({FFTTTTTF},False),({FFTTTTTT},True),({FTFFFFFF},False),({FTFFFFFT},False),({FTFFFFTF},False),({FTFFFFTT},False),({FTFFFTFF},False),({FTFFFTFT},False),({FTFFFTTF},False),({FTFFFTTT},False),({FTFFTFFF},False),({FTFFTFFT},False),({FTFFTFTF},False),({FTFFTFTT},False),({FTFFTTFF},False),({FTFFTTFT},False),({FTFFTTTF},False),({FTFFTTTT},True),({FTFTFFFF},False),({FTFTFFFT},False),({FTFTFFTF},False),({FTFTFFTT},False),({FTFTFTFF},False),({FTFTFTFT},False),({FTFTFTTF},False),({FTFTFTTT},True),({FTFTTFFF},False),({FTFTTFFT},False),({FTFTTFTF},False),({FTFTTFTT},True),({FTFTTTFF},False),({FTFTTTFT},False),({FTFTTTTF},False),({FTFTTTTT},True),({FTTFFFFF},False),({FTTFFFFT},False),({FTTFFFTF},False),({FTTFFFTT},True),({FTTFFTFF},False),({FTTFFTFT},False),({FTTFFTTF},False),({FTTFFTTT},True),({FTTFTFFF},False),({FTTFTFFT},False),({FTTFTFTF},False),({FTTFTFTT},True),({FTTFTTFF},True),({FTTFTTFT},True),({FTTFTTTF},True),({FTTFTTTT},True),({FTTTFFFF},False),({FTTTFFFT},False),({FTTTFFTF},False),({FTTTFFTT},True),({FTTTFTFF},True),({FTTTFTFT},True),({FTTTFTTF},True),({FTTTFTTT},True),({FTTTTFFF},True),({FTTTTFFT},True),({FTTTTFTF},True),({FTTTTFTT},True),({FTTTTTFF},True),({FTTTTTFT},True),({FTTTTTTF},True),({FTTTTTTT},True),({TFFFFFFF},False),({TFFFFFFT},False),({TFFFFFTF},False),({TFFFFFTT},False),({TFFFFTFF},False),({TFFFFTFT},False),({TFFFFTTF},False),({TFFFFTTT},False),({TFFFTFFF},False),({TFFFTFFT},False),({TFFFTFTF},False),({TFFFTFTT},False),({TFFFTTFF},False),({TFFFTTFT},False),({TFFFTTTF},False),({TFFFTTTT},True),({TFFTFFFF},False),({TFFTFFFT},False),({TFFTFFTF},False),({TFFTFFTT},False),({TFFTFTFF},False),({TFFTFTFT},False),({TFFTFTTF},False),({TFFTFTTT},True),({TFFTTFFF},False),({TFFTTFFT},False),({TFFTTFTF},False),({TFFTTFTT},True),({TFFTTTFF},False),({TFFTTTFT},False),({TFFTTTTF},False),({TFFTTTTT},True),({TFTFFFFF},False),({TFTFFFFT},False),({TFTFFFTF},False),({TFTFFFTT},True),({TFTFFTFF},False),({TFTFFTFT},False),({TFTFFTTF},False),({TFTFFTTT},True),({TFTFTFFF},False),({TFTFTFFT},False),({TFTFTFTF},False),({TFTFTFTT},True),({TFTFTTFF},True),({TFTFTTFT},True),({TFTFTTTF},True),({TFTFTTTT},True),({TFTTFFFF},False),({TFTTFFFT},False),({TFTTFFTF},False),({TFTTFFTT},True),({TFTTFTFF},True),({TFTTFTFT},True),({TFTTFTTF},True),({TFTTFTTT},True),({TFTTTFFF},True),({TFTTTFFT},True),({TFTTTFTF},True),({TFTTTFTT},True),({TFTTTTFF},True),({TFTTTTFT},True),({TFTTTTTF},True),({TFTTTTTT},True),({TTFFFFFF},False),({TTFFFFFT},False),({TTFFFFTF},False),({TTFFFFTT},True),({TTFFFTFF},False),({TTFFFTFT},False),({TTFFFTTF},False),({TTFFFTTT},True),({TTFFTFFF},False),({TTFFTFFT},False),({TTFFTFTF},False),({TTFFTFTT},True),({TTFFTTFF},True),({TTFFTTFT},True),({TTFFTTTF},True),({TTFFTTTT},True),({TTFTFFFF},False),({TTFTFFFT},False),({TTFTFFTF},False),({TTFTFFTT},True),({TTFTFTFF},True),({TTFTFTFT},True),({TTFTFTTF},True),({TTFTFTTT},True),({TTFTTFFF},True),({TTFTTFFT},True),({TTFTTFTF},True),({TTFTTFTT},True),({TTFTTTFF},True),({TTFTTTFT},True),({TTFTTTTF},True),({TTFTTTTT},True),({TTTFFFFF},False),({TTTFFFFT},False),({TTTFFFTF},False),({TTTFFFTT},True),({TTTFFTFF},False),({TTTFFTFT},False),({TTTFFTTF},False),({TTTFFTTT},True),({TTTFTFFF},False),({TTTFTFFT},False),({TTTFTFTF},False),({TTTFTFTT},True),({TTTFTTFF},True),({TTTFTTFT},True),({TTTFTTTF},True),({TTTFTTTT},True),({TTTTFFFF},False),({TTTTFFFT},False),({TTTTFFTF},False),({TTTTFFTT},True),({TTTTFTFF},True),({TTTTFTFT},True),({TTTTFTTF},True),({TTTTFTTT},True),({TTTTTFFF},True),({TTTTTFFT},True),({TTTTTFTF},True),({TTTTTFTT},True),({TTTTTTFF},True),({TTTTTTFT},True),({TTTTTTTF},True),({TTTTTTTT},True)]
-}

-- Thus, one (rather brute force) way of reducing the search space in
-- the generation of all proper algorithms, is to only start with
-- indices which give different functions - like 1,4,7 here instead of
-- [1..9] - already a big win. It may be possible to do an even better
-- job but this could be a good start.
