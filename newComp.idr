module Main
import Data.Vect

data TyExp
    = Tnat 
    | Tbool

total
Val : TyExp -> Type
Val Tnat = Nat
Val Tbool = Bool

data Exp : TyExp -> Type where
  ExpVal : Val t -> Exp t
  ExpAddition : Exp Tnat -> Exp Tnat -> Exp Tnat
  ExpSubtraction : Exp Tnat -> Exp Tnat -> Exp Tnat
  ExpMultiplication : Exp Tnat -> Exp Tnat -> Exp Tnat
  ExpIfThenElse : Exp Tbool -> Exp a -> Exp a -> Exp a
  ExpOr : Exp Tbool -> Exp Tbool -> Exp Tbool
  ExpAnd : Exp Tbool -> Exp Tbool -> Exp Tbool

total
eval : Exp t -> Val t
eval (ExpVal x) = x
eval (ExpAddition x y) = eval x + eval y
eval (ExpSubtraction x y) = minus (eval x) (eval y)
eval (ExpMultiplication x y) = eval x * eval y
eval (ExpIfThenElse x y z) = case eval x of
                                  True => eval y
                                  False => eval z
eval (ExpOr x y) = case eval x of
                        False => eval y
                        True => True
eval (ExpAnd x y) = case eval x of
                        True => eval x
                        False => False

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

data BinBoolOp
    = OR
    | AND

data Code : StackType n1 -> StackType n2 -> Type where
  SKIP : Code init init 
  COMBINE : Code init mid -> Code mid ret -> Code init ret
  PUSH : Val ret -> Code init (ret :: init)
  POP : Code (ret :: init) init
  ADD : Code(Tnat :: Tnat :: init) (Tnat :: init)
  SUB : Code(Tnat :: Tnat :: init) (Tnat :: init)
  MULT : Code(Tnat :: Tnat :: init) (Tnat :: init)
  IFTHENELSE : Code n m -> Code n m -> Code(Tbool :: n) m
  BINBOOLOP : BinBoolOp -> Code (Tbool :: Tbool :: stk) (Tbool :: stk)

getOp : BinBoolOp -> Bool -> Bool -> Bool
getOp OR y z = case y of
                        False => z
                        True => True
getOp AND y z = case y of
                        True => z
                        False => False

total
exec : Code n m -> StackData n -> StackData m
exec SKIP y = y
exec (COMBINE x z) y = exec z (exec x y)
exec (PUSH x) y = StackCons x y
exec POP (StackCons x y) = y
exec ADD (StackCons x (StackCons y z)) = StackCons (y + x) z
exec SUB (StackCons x (StackCons y z)) = StackCons (minus y x) z
exec MULT (StackCons x (StackCons y z)) = StackCons (y * x) z
exec (IFTHENELSE true false) (StackCons pred z) = if pred then exec true z else exec false z
exec (BINBOOLOP x) (StackCons y (StackCons z w)) = StackCons(getOp x y z) w

total
compile : Exp t -> Code s (t::s)
compile (ExpVal x) = PUSH x
compile (ExpAddition x y) = COMBINE (compile x) (COMBINE (compile y) ADD)
compile (ExpSubtraction x y) = COMBINE (compile x) (COMBINE (compile y) SUB)
compile (ExpMultiplication x y) = COMBINE (compile x) (COMBINE (compile y) MULT)
compile (ExpIfThenElse x y z) = COMBINE (compile x) (IFTHENELSE (compile y) (compile z))
compile (ExpOr x y) = COMBINE (compile x) (COMBINE (compile y) (BINBOOLOP OR))
compile (ExpAnd x y) = COMBINE (compile x) (COMBINE (compile y) (BINBOOLOP AND))

total
evalPath: (e : Exp t) -> Val t
evalPath e = eval(e)

total
compileExecPath: (e : Exp t) -> Val t
compileExecPath e = top(exec(compile(e)) EmptyStack)
