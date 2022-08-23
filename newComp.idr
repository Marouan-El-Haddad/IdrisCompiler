module Main
import Data.Vect

data TyExp
    = Tnat 
    | Tbool

Val : TyExp -> Type
Val Tnat = Nat
Val Tbool = Bool

data Exp : TyExp -> Type where
  ExpVal : Val t -> Exp t
  ExpAddition : Exp Tnat -> Exp Tnat -> Exp Tnat
  ExpSubtraction : Exp Tnat -> Exp Tnat -> Exp Tnat
  ExpMultiplication : Exp Tnat -> Exp Tnat -> Exp Tnat
  ExpIfThenElse : Exp Tbool -> Exp a -> Exp a -> Exp a

eval : Exp t -> Val t
eval (ExpVal x) = x
eval (ExpAddition x y) = eval x + eval y
eval (ExpSubtraction x y) = minus (eval x) (eval y)
eval (ExpMultiplication x y) = eval x * eval y
eval (ExpIfThenElse x y z) = case eval x of
                                  True => eval y
                                  False => eval z


--eval (ExpIfThenElse x y z) = eval z

--So T is a TyExp, 
--Val T is a concrete Type, 
--v is a value of that type, 
--and val v is an Exp storing v


--Having the data adds the need for the data constructor, but it allows Idris to work backward 
--(infer t knowing some type in position of a hole Val t) whereas the function form doesn't. 
--Like I said, I wouldn't be surprised if the function form gets you pretty far along an interpreter/compiler implementation, 
--but having the data representation can make Idris inference simpler (or at least more Haskell-like, 
--since I've yet to run out of ways to put DPairs to use in Idris type schemes).

--I'd say the function form is "simpler" if you can get away with it, and I think Idris syntax is really nice in enabling you to "upgrade" 
--to the data version with low pain if it turns out to be useful 
--(I think they call it the uniform access principle: note you didn't have to touch Exp to make the change).



{-
data TyExp
    = Tnat 
    | Tbool

data Val: TyExp -> Type where
  ValTnat: Nat -> Val Tnat
  ValTbool: Bool -> Val Tbool

data Exp : TyExp -> Type where
  ExpVal : Val t -> Exp t
  ExpAddition : Exp Tnat -> Exp Tnat -> Exp Tnat
  ExpSubtraction : Exp Tnat -> Exp Tnat -> Exp Tnat
  ExpMultiplication : Exp Tnat -> Exp Tnat -> Exp Tnat
  ExpIfThenElse : Exp Tbool -> Exp a -> Exp a -> Exp a
-}
