{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
module EmptyTypeNats (module EmptyTypeNats,
                      Nat, KnownNat, natVal, Proxy(Proxy), sameNat, (:~:)(Refl)) where
import Data.Data (Proxy(Proxy))
import Data.Type.Equality((:~:)(Refl))
import GHC.TypeNats
--The successor type we need for algorithms and tuples (to keep track of correct sizes)

type Z = 0
type S (n::Nat) = 1+n
-- type S n = n+1
type Two = 2
type Three = 3
type Nine = 9
type Mul m n = (GHC.TypeNats.*) m n
type Add m n = (GHC.TypeNats.+) (m::Nat) (n::Nat)


{-
type family (*) (a :: Nat) (b :: Nat) :: Nat
type family (+) (a :: Nat) (b :: Nat) :: Nat
type family (-) (a :: Nat) (b :: Nat) :: Nat
type (<=) (x :: Nat) (y :: Nat) = (x <=? y) ~ 'True :: Constraint
type family (<=?) (a :: Nat) (b :: Nat) :: Bool
type family CmpNat (a :: Nat) (b :: Nat) :: Ordering
type family Div (a :: Nat) (b :: Nat) :: Nat
class KnownNat (n :: Nat) where
  GHC.TypeNats.natSing :: GHC.TypeNats.SNat n
  {-# MINIMAL natSing #-}
type family Log2 (a :: Nat) :: Nat
type family Mod (a :: Nat) (b :: Nat) :: Nat
data SomeNat
  = forall (n :: Nat). KnownNat n => SomeNat (Data.Proxy.Proxy n)
type family (^) (a :: Nat) (b :: Nat) :: Nat
natVal :: KnownNat n => proxy n -> GHC.Natural.Natural
natVal' ::
  KnownNat n =>
  ghc-prim-0.5.3:GHC.Prim.Proxy# n -> GHC.Natural.Natural
sameNat ::
  (KnownNat a, KnownNat b) =>
  Data.Proxy.Proxy a
  -> Data.Proxy.Proxy b -> Maybe (a Data.Type.Equality.:~: b)
someNatVal :: GHC.Natural.Natural -> SomeNat
data Nat
-}

{-
data S n 
data Z   
type One    = S Z
type Two    = S One
type Three  = S Two
type Four   = S Three
type Five   = S Four
type Six    = S Five
type Seven  = S Six
type Eight  = S Seven
type Nine   = S Eight

data Mul m n where
-}
{-
class ValueOf n where val :: n -> Int
instance ValueOf Z where val = const 0
instance ValueOf n => ValueOf (S n) where val
-}
