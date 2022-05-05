{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Tuple (module Tuple, module EmptyTypeNats, module DSLsofMath.Algebra) where
import Prelude hiding (Num(..),Fractional(..), fromIntegral)
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
