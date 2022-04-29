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

type REAL = Double
---------------- Tuples and Boolean functions ----------------
newtype Tup (n::Nat) a = T {unT :: [a]}
  deriving Eq
type Tuple n = Tup n Bool
{- Possible alternative implementations:
  Int -> a     -- just the indexing implementation
  Fin n -> a   -- indexing with stronger type
-}

type Index = Int

index :: Tup n a -> Index -> a
index (T as) i | i > n = error ("index: i="++show i++" > n="++show n)
               | i < 1 = error ("index: i="++show i++" < 1")
               | otherwise = as!!(i-1)
  where n = length as


instance Functor (Tup n) where fmap = mapTup
mapTup :: (a->b) -> Tup n a -> Tup n b
mapTup f (T ts) = T (map f ts)

-- Example values
t, f :: Bool
t = True; f = False
tt, tf, ft, ff :: Tuple Two
tt = T [t, t]; tf = T [t, f]
ft = T [f, t]; ff = T [f, f]
tff,tft,ftf,fff :: Tuple Three
tff = T [t,f,f]
tft = T [t,f,t]
ftf = T [f,t,f]
fff = T [f,f,f]

type BoolFun n = Tuple n -> Bool
--data Fin n = Int, do later to handle generators properly

-- 1-indexed
insBit :: Index -> Bool -> BoolFun (S n) -> BoolFun n
insBit i b f = f . insert i b

insert :: Index -> a -> Tup n a -> Tup (S n) a
insert i' b (T t) = T (take i t ++ b : drop i t)
  where i = i'-1 -- adjust from 1-indexed to 0-indexed take and drop

remove :: Index -> Tup (S n) a -> Tup n a
remove i (T t) = T (take (i-1) t ++ drop i t)
   -- remove 2 [a1,a2,a3,a4] = [a1,a3,a4]

---------------- SHOW INSTANCES ----------------
-- instance Show a => Show (Tup n a) where  show = showTup

showTup :: Show a => Tup n a -> String
showTup (T bs) = "{"++map (head . show) bs++"}"


instance Show (Tuple n) where  show = showTuple
showTuple :: Tuple n -> String
showTuple (T bs) = "{"++map (head . show) bs++"}"  -- TODO this is a hack for printing Bool
instance Read (Tuple n) where  readsPrec = readsPrecTuple
readsPrecTuple :: Int -> ReadS (Tuple n)
readsPrecTuple _p "" = []
readsPrecTuple _p text | ok = [(T (map c2b cs), tail end)]
                       | otherwise = []
  where  ok = head text == '{' && head end == '}'
         (cs, end) = span (\c-> c == 'T' || c == 'F') (tail text)

c2b :: Char -> Bool
c2b 'T' = True
c2b 'F' = False
c2b c   = error ("c2b: unexpected character: "++[c])

readTest1 :: Tuple Three
readTest1 = read "{TFT}"

{-
More tests:

λ> univ :: [Tuple Two]
[{FF},{FT},{TF},{TT}]
λ> univ :: [Tuple Three]
[{FFF},{FFT},{FTF},{FTT},{TFF},{TFT},{TTF},{TTT}]
λ> idx (read "{TFT}" :: Tuple Three)
5

-}

----------------
-- Tuples are finite (implements enumeration)
instance (KnownNat n, Fin a) => Fin (Tup n a) where univ = univTupN; idx = idxTupN

univTupN :: (KnownNat n, Fin a) => [Tup n a]
univTupN = xs
  where  nN = natVal (typeHelper (head xs))
         xs = univVecN nN

typeHelper :: Tup n a -> Proxy n
typeHelper _ = Proxy

univVecN :: Fin a  => Natural -> [Tup n a]
univVecN n | fromIntegral n == (0::Int)  = [T []]
           | otherwise            = [T (a:bs) | a <- univ, T bs <- univVecN (pred n)]

idxTupN :: (KnownNat n, Fin a) => Tup n a -> Int
idxTupN (T as) = baseNtoInt cardA (map idx as) -- map gives the "base (card a)" repRes entation of the index
  where cardA = length (univ `asTypeOf` as)

baseNtoInt :: Int -> [Int] -> Int
baseNtoInt b [] = 0
baseNtoInt b (i:is) = i + b*baseNtoInt b is

{-
instance (Fin a, Fin (Tup n a)) => Fin (Tup (S n) a) where
  univ = univTup univ
  idx  = idxTup idx univ
-}
-- univTup :: Fin a => [Tup n a] -> [Tup (S n) a]
univTup ts = [ T (a:b) | a <- univ, T b <- ts ]

idxTup :: Fin a => (Tup n a -> Int) -> [Tup n a] -> (Tup (S n) a -> Int)
idxTup i ts (T (a:bs)) = idx a * card ts + i (T bs)
  where card = length

{-
instance Fin (Tuple n) => Fin (Tuple (S n)) where
  univ       = univTuple univ
  idx        = idxTuple idx univ

univTuple :: [Tuple n] -> [Tuple (S n)]
univTuple ts = [ T (a:b) | a <- univ, T b <- ts ]

idxTuple :: (Tuple n -> Int) -> [Tuple n] -> (Tuple (S n) -> Int)
idxTuple i ts (T (a:bs)) = idx a * card ts + i (T bs)
  where card = length
-}

---------------- ALGORITHMS DEFINITION ----------------
data Alg (n :: Nat) where -- should have arguments n and f
--  Done :: Alg n -- Alg n (const b)
  Res :: Bool -> Alg n -- new constructor
  Pick :: KnownNat n => Index -> Alg n -> Alg n -> Alg (S n)

eqAlg :: Alg n -> Alg n -> Bool
eqAlg (Res b) (Res b') = b==b'
eqAlg (Pick i iF iT) (Pick j jF jT) = i==j && case sameNat (alg2Proxy iF) (alg2Proxy jF) of
  Nothing    -> False -- should never happen
  Just Refl  -> eqAlg iF jF && eqAlg iT jT
eqAlg _ _ = False

instance Eq (Alg n) where (==) = eqAlg

cmpThen :: Ordering -> Ordering -> Ordering
cmpThen LT _ = LT
cmpThen EQ y = y
cmpThen GT _ = GT

cmpAlg :: Alg n -> Alg n -> Ordering
cmpAlg (Res b) (Res b') = compare b b'
cmpAlg (Pick i iF iT) (Pick j jF jT) = cmpThen (compare i j) $ case sameNat (alg2Proxy iF) (alg2Proxy jF) of
  Nothing    -> error "cmpAlg: subtrees of different index should never happen"
  Just Refl  -> cmpThen (cmpAlg iF jF) (cmpAlg iT jT)
cmpAlg (Res _) (Pick _ _ _) = LT
cmpAlg (Pick _ _ _) (Res _) = GT

instance Ord (Alg n) where compare = cmpAlg

-- d = Done
df = Res f
dt = Res t

-- pick is a "smart constructor" which adjusts the "global" indeces to
-- match the shorter tuples further down in the tree (to avoid
-- indexing out of bounds).
pick :: KnownNat n => Index -> Alg n -> Alg n -> Alg (S n)
pick i aF aT = Pick i (fix i aF) (fix i aT)

-- the indeces in the input Alg are adjusted if they are above i
fix :: Index -> Alg n -> Alg n
-- fix i Done            = Done
fix i (Res b)         = Res b
fix i (Pick j aF aT) | i<j        = Pick (j-1) (fix i     aF) (fix i     aT)
                     | i==j       = error "pick: cannot pick the same index twice"
                     | otherwise  = Pick  j    (fix (i-1) aF) (fix (i-1) aT)
{-
Precondition: 1<=i<=n and no index is asked twice.
When calling fix recursively, the first arg. must be <=n-1
In the case when i>j we need to reduce it.
-}

{-
unfix

When printing an algorithm it is helpful if the indices are printed
with reference to positions in the full tuple at the top level and not
the position in the local, reduced, tuple. (The local position is
needed to avoid indexing out of bounds and it useful for keeping the
complexity down.)

I think keeping a list of "seen global indices" when recursing down
should be enough. Then we can translate the local indices based on
this "path".

Example: (with P = Pick and d = Res _)

  P 1 (P 2 (P 1 d d) d) (P 1 d d)
translates to
  P 1 (P 3 (P 2 d d) d) (P 2 d d)
because the outermost Pick 1 "removes" position 1 from the tuple and
"unfix" puts it back in.

Better idea: start with the list rem=[1..n] at the top and remove
numbers as they are passed. The list should then act as a translator
from local to global. Example: if and alg uses Pick 1 all the way down
the list rem will go from [1..n] -> [2..n] -> [3..n] -> ....

-}
type GAlg = Alg
local2Global :: Tup n Index -> Alg n -> GAlg n
local2Global _rem (Res b) = Res b
local2Global rem (Pick i aF aT) = Pick (index rem i) gF gT
  where  rem' = remove i rem
         gF = local2Global rem' aF
         gT = local2Global rem' aT

unfix' :: KnownNat n => Alg n -> GAlg n
unfix' alg = local2Global (T [1..nN]) alg
  where nN = fromIntegral (natVal (alg2Proxy alg))

{-
-- Old definition of "local to global" index translator - seems to be a bit buggy.

unfix :: [Index] -> Alg n -> Alg n
-- unfix _ Done    = Done
unfix _ (Res b) = Res b
unfix path (Pick i aF aT) = Pick j (rec aF) (rec aT)
  where  j = iLToIndexMap path i
         rec = unfix (i:path)
--  where  j = translateIndex path i
--         rec = unfix (extendPath j path)

extendPath :: Eq a => a -> [a] -> [a]
extendPath j path | elem j path = error "extendPath: duplicate index"
                  | otherwise   = j:path

translateIndex :: [Index] -> Index -> Index
translateIndex path i = i + length (filter (<=i) path)


iLToIndexMap :: [Index] -> Index -> Index
iLToIndexMap [] = id
-- iLToIndexMap (i:is) = iLToIndexMap is . remap i
iLToIndexMap (i:is) = remap i . iLToIndexMap is

remap :: Index -> (Index -> Index)
remap i = \j -> if j<i then j else j+1

-- TODO Better definition needed:
-- Examples:
--   visiting 1,2,3 -> local 1 is adjusted to global 4
--   visiting 2,3,1 -> local 1 is adjusted to global 4
--   visiting 2,3,4 -> local 1 is not adjusted, local 2 is adjusted to global 5
--   visiting 3,4,2 -> local 1 is not adjusted, local 2 is adjusted to global 5
-- We need to look at the visited indices (one by one?) and adjust i as we go.
--
-- invariant: local position i is in the tuple you get by remove i1 . remove i2 . ...
--   where all the i's are local indices.
-}
{-
Idea: update a "current index map" at each level. The map should take local index at level k to the top level n
Starting point (k=n) is the identity function
After Pick 1, the first position is gone, which means that the function is now (1+)
After Pick 2, the function maps 1 to 1, 2.. to one more.
After Pick i, then function maps j<i to itself, j>=i to one more
Basically remaps the indices to "make place" for a slot at position i

remap i = \j -> if j<i then j else j+1

-}


----------------

cost :: Alg n -> Tuple n -> Int
-- cost Done            _  = 0
cost (Res _)         _  = 0
cost (Pick i aF aT)  x  = 1 + if index x i then cost aT x' else cost aF x'
   where x' = remove i x

-- predicate to check that a "candidate algorithm" satisfies the alg. rules
properAlg :: KnownNat n => BoolFun n -> Alg n -> Bool
-- properAlg f Done = isConst f
properAlg f (Res b) = f == const b
properAlg f (Pick i aF aT) = notConst f && left && right
  where  left   = properAlg (insBit i False f) aF
         right  = properAlg (insBit i True  f) aT

help :: String -> Bool -> Maybe String
help err False = Just err
help err True  = Nothing

Nothing &&& my = my
mx &&& Nothing = mx
Just err1 &&& Just err2 = Just (err1 ++ ", " ++ err2)

-- Nothing means "no complaints"
-- Just err means "this is the problem"
properAlg' :: KnownNat n => BoolFun n -> Alg n -> [(Index,Bool)] -> Maybe String
-- properAlg' fun Done xs = help ("Done {f = "++show fun++"}: "++show xs) (isConst fun)
properAlg' fun (Res b) xs = help ("Res "++show b++" {f = "++show fun++"}: "++show xs) (fun == const b)
properAlg' fun (Pick i aF aT) xs = help ("Pick "++show i++" const: " ++ show xs) (notConst fun)
                              &&& left &&& right
  where  left   = properAlg' (insBit i f fun) aF ((i,f):xs)
         right  = properAlg' (insBit i t fun) aT ((i,t):xs)

notConst :: Fin (Tuple n) => BoolFun n -> Bool
notConst = not . isConst

isConst :: Fin (Tuple n) => BoolFun n -> Bool
isConst f = isConstL (map f univ)

isConstL [] = True
isConstL (x:xs) = all (x==) xs

fFromAlg :: Alg n -> Tuple n ->  Bool
fFromAlg (Res b) _ = b
fFromAlg (Pick i aF aT) t = if b then fFromAlg aT t' else fFromAlg aF t'
  where  b  = index t i
         t' = remove i t

{-
data Alg n f where  -- type family indexed by n and f
    Done :: Alg n (const b)
    Pick :: Fin n -> Alg n     (insBit i False f) ->
                     Alg n     (insBit i True f)  ->
                     Alg (n+1) f

The example algorithm alg1 :: Alg Two from above:
      Pick 0     -- Alg 2 and_2
     /     \
   Done    Pick 1  -- Alg 1 (const False),   Alg 1 (and_1)
           /     \
         Done   Done -- Alg 0 _

insBit 0 False and_2 == const False :: Tuple 1 -> Bool
insBit 0 True  and_2 == and_1       :: Tuple 1 -> Bool

a :: Alg n f means
  a is an algorithm for f : Tuple n -> Bool
We have two cases:
  Done - only allowed if the function is actually constant
  Pick i fa ta
    where you pick one index i to look at
      then, if the tuple value at i is false, cont. with fa
      otherwise, continue with ta
  Both fa and ta are for boolean functions on one less bit.
  And they are for other "sub-functions" of f:
    ff where that picked index is fixed to False
    ft where that picked index is fixed to True

-}

-- instance KnownNat n => Show (Alg n) where show = ("local: "++).show2

instance KnownNat n => Show (Alg n) where show = ("global: "++).show3

-- Want to do source code for tree in Tikz, seems to work now!
-- But some indices seem a bit wrong
{-
*GenAlg> putStr $ show5 (algsAC!!2)
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
