{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Alg.Show where
import Prelude hiding (Num(..),Fractional(..), fromIntegral)
import Data.List (intersperse)
import Numeric.Natural -- (Natural)
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

-- end of core types and functions
----------------
