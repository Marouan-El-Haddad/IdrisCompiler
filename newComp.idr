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

total
StackDepth : Type
StackDepth = Nat

total
StackType : StackDepth -> Type
StackType n = Vect n TyExp

data StackData : StackType n -> Type where
  EmptyStack : StackData Nil
  StackCons : Val x -> StackData xs -> StackData (x :: xs)

total
top : StackData (x :: xs) -> Val x
top (StackCons y z) = y

data Code : StackType n1 -> StackType n2 -> Type where
  SKIP : Code init init 
  COMBINE : Code init mid -> Code mid ret -> Code init ret
  PUSH : Val ret -> Code init (ret :: init)
  POP : Code (ret :: init) init
  ADD : Code(Tnat :: Tnat :: init) (Tnat :: init)
  SUB : Code(Tnat :: Tnat :: init) (Tnat :: init)
  MULT : Code(Tnat :: Tnat :: init) (Tnat :: init)
  IfThenElse : Code n m -> Code n m -> Code(Tbool :: n) m

total
exec : Code n m -> StackData n -> StackData m
exec SKIP y = y
exec (COMBINE x z) y = exec z (exec x y)
exec (PUSH x) y = StackCons x y
exec POP (StackCons x y) = y
exec ADD (StackCons x (StackCons y z)) = StackCons (y + x) z
exec SUB (StackCons x (StackCons y z)) = StackCons (minus y x) z
exec MULT (StackCons x (StackCons y z)) = StackCons (y * x) z
exec (IfThenElse x z) (StackCons True w) = exec x w
exec (IfThenElse x z) (StackCons False w) = exec z w


{-
exec SKIP y = ?exec_rhs_0
exec (COMBINE x z) y = ?exec_rhs_1
exec (PUSH x) y = ?exec_rhs_2
exec POP y = ?exec_rhs_3
exec ADD y = ?exec_rhs_4
exec SUB y = ?exec_rhs_5
exec MULT y = ?exec_rhs_6
exec (IfThenElse x z) y = ?exec_rhs_7
-}


{-exec (Combine x y) xs = exec y (exec x xs)
exec (Push x) xs = x::xs
exec Add (x0::x1::xs) = (x1 + x0) :: xs
exec Sub (x0::x1::xs) = (x1 - x0) :: xs
exec Mult (x0::x1::xs) = (x1 * x0) :: xs
exec Pop (x :: xs) = xs
--exec (IfThenElse _ _) _ = ?exec_missing_case_1
-}


{-total
compile : Expr -> Code k (S k)
compile (EIntLit x) = Push x
compile (EAddition x y) = Combine (compile x) (Combine (compile y) Add)
compile (ESubtraction x y) = Combine (compile x) (Combine (compile y) Sub)
compile (EMultiplication x y) = Combine (compile x) (Combine (compile y) Mult)
--compile (EIfThenElse x y a b) = ?compile_missing_case_1
-}

--top EmptyStack = ?top_rhs_0
--top (StackCons x y) = top y

--All Val StackType

--top : Stack (S n) -> Int
--top (x :: xs) = x

{-
data Code : StackDepth -> StackDepth -> Type where
    Combine : Code a b -> Code b c -> Code a c
    Push : TyExp -> Code n (S n)
    Add : Code (S (S n)) (S n)
    Sub : Code (S (S n)) (S n)
    Mult : Code (S (S n)) (S n)
    Pop : Code (S n) n
    -}

--eval (ExpIfThenElse x y z) = eval z
--So T is a TyExp, 
--Val T is a concrete Type, 
--v is a value of that type, 
--and val v is an Exp storing v


--Having the data adds the need for the data constructor, but it allows Idris to work backward 
--(infer ret knowing some type in position of a hole Val ret) whereas the function form doesn'ret. 
--Like I said, I wouldn'ret be surprised if the function form gets you pretty far along an interpreter/compiler implementation, 
--but having the data representation can make Idris inference simpler (or at least more Haskell-like, 
--since I've yet to run out of ways to put DPairs to use in Idris type schemes).

--I'd say the function form is "simpler" if you can get away with it, and I think Idris syntax is really nice in enabling you to "upgrade" 
--to the data version with low pain if it turns out to be useful 
--(I think they call it the uniform access principle: note you didn'ret have to touch Exp to make the change).



{-
data TyExp
    = Tnat 
    | Tbool

data Val: TyExp -> Type where
  ValTnat: Nat -> Val Tnat
  ValTbool: Bool -> Val Tbool

data Exp : TyExp -> Type where
  ExpVal : Val ret -> Exp ret
  ExpAddition : Exp Tnat -> Exp Tnat -> Exp Tnat
  ExpSubtraction : Exp Tnat -> Exp Tnat -> Exp Tnat
  ExpMultiplication : Exp Tnat -> Exp Tnat -> Exp Tnat
  ExpIfThenElse : Exp Tbool -> Exp a -> Exp a -> Exp a
-}
