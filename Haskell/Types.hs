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
module Types (module Types, module EmptyTypeNats, module DSLsofMath.Algebra) where
import qualified Prelude
import Prelude (
  Read, read, ReadS, String, Char, print,
  Eq((==)), (>), (<), (<=),
  Maybe(Nothing, Just),
  Show, show,
  Functor(fmap),
  Foldable,
  Bool(False, True), (&&), (||), not, otherwise, and,
  Ord, compare, Ordering(LT,EQ,GT),
  Int, divMod, div, Integral, pred,
  Double, Rational,
  (.), id, const, error, asTypeOf, ($),
  head, all, concatMap, map, (!!), (++), length, tail,
  even, odd, max,
  splitAt, span, drop, take, repeat, replicate,
  foldr, filter, zipWith, elem, maximum, concat,
  undefined,
  putStrLn, IO)
import Data.List (intersperse)
import Numeric.Natural -- (Natural)
import DSLsofMath.Algebra
import DSLsofMath.PSDS
import EmptyTypeNats
import FiniteEnum
import Tuple
import Alg
------------------------------------------------------ SHOW FUNCTIONS -----------------------------------------------------
instance KnownNat n => Show (Alg n) where show = ("global: "++).show3

-- Want to do source code for tree in Tikz, seems to work now!
-- But some indices seem a bit wrong
{-*GenAlg> putStr $ show5 (algsAC!!2)
[$x_1$, root 
[$x_2$, EL = 0 [$x_3$, EL = 0 [$x_4$, EL = 0 [$x_5$, EL = 0 [1, EL = 0 ][0, EL = 1 ]][$x_5$, EL = 1 [0, EL = 0 ][1, EL = 1 ]]][1, EL = 1 ]][1, EL = 1 ]]
[$x_2$, EL = 1 [1, EL = 0 ][$x_4$, EL = 1 [$x_4$, EL = 0 [1, EL = 0 ][$x_5$, EL = 1 [1, EL = 0 ][0, EL = 1 ]]][$x_5$, EL = 1 [$x_5$, EL = 0 [1, EL = 0 ][0, EL = 1 ]][1, EL = 1 ]]]]]


Suggestion: use these macros:
\newcommand{\algroot}[3]{[\ensuremath{x_{#1}}, root #2 #3]}
\newcommand{\algnode}[4]{[\ensuremath{x_{#1}}, EL = #2 #3 #4]}
\newcommand{\algleaf}[2]{[#1, EL = #2]}

and generate calls to them with algFigRoot

When it works, you can add an argument for color
-}

algFigRoot :: KnownNat n => GAlg n -> String 
algFigRoot (Pick i aF aT)   = "\\algroot{" ++ show i ++ "}{" ++ algFigRest 0 aF ++ "}{" ++ algFigRest 1 aT ++ "}"

algFigRest :: KnownNat n => Int -> GAlg n -> String
algFigRest p (Pick i aF aT) = "\\algnode{" ++ show i ++ "}{"++show p++"}{" ++ algFigRest 0 aF ++ "}{" ++ algFigRest 1 aT ++ "}"
algFigRest p (Res False)    = "\\algleaf{0}{" ++ show p ++ "}"
algFigRest p (Res True)     = "\\algleaf{1}{" ++ show p ++ "}"

show5 :: KnownNat n => Alg n -> String
show5 = showtop . unfix'

showtop :: Alg n -> String 
showtop (Pick i a1 a2) = "[$x_" ++ show i ++ "$, root " ++ "\n["++ showrest a1 ", EL = 0 " ++ "\n["++ showrest a2 ", EL = 1 " ++ "]" 

showrest :: Alg n -> String -> String 
showrest (Res b) s | b          = "1" ++ s ++ "]"
                   | otherwise  = "0"  ++ s ++ "]"
showrest (Pick i a1 a2) s = "$x_" ++ show i ++ "$" ++ s ++ "["++ showrest a1 ", EL = 0 " ++ "[" ++ showrest a2 ", EL = 1 " ++ "]"


-- unfix is buggy - see above.
show3 :: KnownNat n => Alg n -> String
show3 = show2 . unfix'

show2 :: Alg n -> String
-- show2 Done = "d"
show2 (Res b) = showBit b
show2 (Pick i a1 a2)   = "[" ++ show2 a1 ++"<-"++ show i++"->" ++ show2 a2 ++ "]"

showBit False = "f"
showBit True  = "t"

show1 :: Alg n -> String
-- show1 Done = ""
show1 (Res b) = showBit b
show1 (Pick i a1 (Res _)) = "P"++show i ++ "{" ++ show1 a1 ++ "}\n"  -- TODO handle Res constructor better
show1 (Pick i (Res _) a2) = "P"++show i ++ "{" ++ show1 a2 ++ "}"    -- TODO handle Res constructor better
show1 (Pick i a1 a2)   = "P"++show i ++ "{" ++ show1 a1 ++"}{" ++ show1 a2 ++ "}"


   --"(" ++ "Pick " ++ show i ++ " " ++ show a1 ++ " " ++ show a2 ++ ")"


{-
2D pretty-printing of "algorithms":
Res b -> showBit b
Pick i x y ->   i
 left right
-}

data Block = Block {height :: Int, width :: Int, payload :: [String]}

singBlock :: String -> Block
singBlock s = Block 1 (length s) [s]

tree :: String -> Block -> Block -> Block
tree s l r = l' + tee (singBlock s) h + r'
  where  (+) = beside
         l' = shiftDown l
         r' = shiftDown r
         h  = max (height l) (height r)
-- above    :: Block -> Block -> Block
tee b h = Block (height b + h) (max (width b) 1) (payload b ++ replicate h " ")
shiftDown :: Block -> Block
shiftDown (Block h w p) = Block (h+1) w (replicate w ' ':p)


beside :: Block -> Block -> Block
beside l r = Block (length pay) (maximum (map length pay)) pay
  where pay = take hei (zipWith (++) (payload l++repeat padl) (payload r++repeat padr))
        wl = width l; padl = replicate wl ' '
        wr = width r; padr = replicate wr ' '
        hei = max (height l) (height r)

render :: Block -> String
render (Block h w p) = concat (intersperse "\n" p)
pretty :: Alg n -> Block
pretty (Res b) = singBlock (showBit b)
pretty (Pick i l r) =  tree (show i) left right
  where  left  = pretty l
         right = pretty r

printAlg :: KnownNat n => Alg n -> IO ()
printAlg = putStrLn . render . pretty . unfix'

{-
λ> printAlg algmaj
     1
 2       2
f  3   3  t
  f t f t

λ> printAlg algABC
                                           1
                                         2   2
                                       3  t t  3
                   4                    t     t                    4
         5                   5                           5                   5
 6               6         6   6                 6               6         6   6
t    7       7    t    7    t t    7            t    7       7    t    7    t t    7
   8   8   8   8     8   8       8   8             8   8   8   8     8   8       8   8
  t f f t t f f t   t f f t     t f f t           t f f t t f f t   t f f t     t f f t

-}

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

alg2Proxy :: Alg n -> Proxy n
alg2Proxy _ = Proxy

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

-- end of core types and functions
----------------
