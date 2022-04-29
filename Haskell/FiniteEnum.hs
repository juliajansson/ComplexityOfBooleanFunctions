{-# LANGUAGE ScopedTypeVariables #-}
module FiniteEnum where

class Fin a where
  univ :: [a]
  idx  :: a -> Int

instance Fin () where
  univ = [()]
  idx () = 0
  
instance Fin Bool where
  univ  = [False, True]
  idx False = 0
  idx True  = 1

instance Fin a => Fin (Maybe a) where
  univ         = Nothing : map Just univ
  idx Nothing  = 0
  idx (Just x) = 1 + idx x

instance (Fin a, Fin b) => Fin (a, b) where
  univ       = [ (a, b) | a <- univ, b <- univ ]
  idx (a, b) = idx a * bCard + idx b
    where bCard = length (univ :: [b])

instance (Fin a, Fin b) => Fin (Either a b) where
  univ          = map Left univ ++ map Right univ
  idx (Left x)  = idx x
  idx (Right y) = length (univ :: [a]) + idx y 

-- TODO check if the idx call in univ can be avoided
instance (Fin a, Fin b) => Fin (a -> b) where
  univ  = [ \a -> bs !! (idx a) | bs <- iterate combs [[]] !! length (univ :: [a]) ]
    where combs ls = [b : bs | b <- univ, bs <- ls]
  idx f = foldl (\x y -> x * bCard + idx (f y)) 0 univ
    where bCard = length (univ :: [b])

instance (Fin a, Show a, Show b) => Show (a -> b) where
  show f = "tab2Fun " ++ show [ (a, f a) | a <- univ ]

tab2Fun :: (Eq a, Show a) => [(a,b)] -> a -> b
tab2Fun tab a = case lookup a tab of
                  Just x -> x
                  Nothing -> error ("tab2Fun: "++show a++" not found")


instance (Fin a, Eq b) => Eq (a -> b) where  (==) = eqFinFun

type EQ a = a -> a -> Bool

eqFinFun :: (Fin a, Eq b) => EQ (a->b)
eqFinFun f g = all (\tup -> f tup == g tup) univ
