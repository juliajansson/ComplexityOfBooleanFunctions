{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Alg (module Alg, module Tuple) where
import Prelude hiding (Num(..),Fractional(..), fromIntegral)
import Tuple
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

alg2Proxy :: Alg n -> Proxy n
alg2Proxy _ = Proxy