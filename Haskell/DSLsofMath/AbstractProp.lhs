\begin{code}
module DSLsofMath.AbstractProp where
data Falsity
data Truth   -- = ()
data And p q -- = (p,q)
data Or a b  -- = Either a b
type Implies p q = p -> q
type Not p = Implies p Falsity

truthIntro  :: Truth
falseElim   :: Falsity -> p
andIntro    :: p -> q -> And p q
andElimL    :: And p q -> p
andElimR    :: And p q -> q
orIntroL    :: p -> Or p q
orIntroR    :: q -> Or p q
orElim      :: Or p q -> (Implies p r) -> (Implies q r) -> r
notIntro    :: Implies p (And q (Not q)) -> Not p
notElim     :: Not (Not p) -> p
implyIntro  :: (p -> q) -> (Implies p q)
implyElim   :: (Implies p q) -> (p -> q)

(truthIntro, falseElim, 
 andIntro, andElimL, andElimR,
 orIntroL, orIntroR, orElim,
 notElim,  notIntro,
 implyIntro, implyElim
 ) = error "abstract rules, only used for type checking"
\end{code}
