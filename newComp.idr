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
  ExpNot : Exp Tbool -> Exp Tbool
  ExpLTE : Exp Tnat -> Exp Tnat -> Exp Tbool
  ExpGTE : Exp Tnat -> Exp Tnat -> Exp Tbool
  ExpLT : Exp Tnat -> Exp Tnat -> Exp Tbool
  ExpGT : Exp Tnat -> Exp Tnat -> Exp Tbool
  ExpEqual : Exp Tnat -> Exp Tnat -> Exp Tbool
  ExpNotEqual : Exp Tnat -> Exp Tnat -> Exp Tbool

total
eval : Exp t -> Val t
eval (ExpVal x) = x
eval (ExpAddition x y) = eval x + eval y
eval (ExpSubtraction x y) = minus (eval x) (eval y)
eval (ExpMultiplication x y) = eval x * eval y
eval (ExpIfThenElse x y z) = if eval x then eval y else eval  z
eval (ExpOr x y) = eval x || eval y
eval (ExpAnd x y) = eval x && eval y
eval (ExpNot x) = not (eval x)
eval (ExpLTE x y) = lte (eval x) (eval y)
eval (ExpGTE x y) = gte (eval x) (eval y)
eval (ExpLT x y) = lt (eval x) (eval y)
eval (ExpGT x y) = gt (eval x) (eval y)
eval (ExpEqual x y) = (eval x) == (eval y)
eval (ExpNotEqual x y) = (eval x) /= (eval y)

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

data CompNatOp
  = LTE 
  | GTE
  | LT
  | GT

data EqualOp
  = EQUAL
  | NOTEQUAL

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
  NOT : Code(Tbool :: init) (Tbool :: init)
  COMPNATOP : CompNatOp -> Code(Tnat :: Tnat :: init) (Tbool :: init)
  EQUALOP : EqualOp -> Code(Tnat :: Tnat :: init) (Tbool :: init)

total
getOp : BinBoolOp -> Bool -> Bool -> Bool
getOp OR y z = y || z
getOp AND y z = y && z

total
getComp : CompNatOp -> Nat -> Nat -> Bool
getComp LTE y z = lte y z
getComp GTE y z = gte y z
getComp LT y z = lt y z
getComp GT y z = gt y z

total
getEqual : EqualOp -> Nat -> Nat -> Bool
getEqual EQUAL y z = y == z
getEqual NOTEQUAL y z = y /= z

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
exec NOT (StackCons x y) = StackCons (not x) y
exec (COMPNATOP x) (StackCons y (StackCons z w)) = StackCons(getComp x y z) w
exec (EQUALOP x) (StackCons y (StackCons z w)) = StackCons(getEqual x y z) w

total
compile : Exp t -> Code s (t::s)
compile (ExpVal x) = PUSH x
compile (ExpAddition x y) = COMBINE (compile x) (COMBINE (compile y) ADD)
compile (ExpSubtraction x y) = COMBINE (compile x) (COMBINE (compile y) SUB)
compile (ExpMultiplication x y) = COMBINE (compile x) (COMBINE (compile y) MULT)
compile (ExpIfThenElse x y z) = COMBINE (compile x) (IFTHENELSE (compile y) (compile z))
compile (ExpOr x y) = COMBINE (compile x) (COMBINE (compile y) (BINBOOLOP OR))
compile (ExpAnd x y) = COMBINE (compile x) (COMBINE (compile y) (BINBOOLOP AND))
compile (ExpNot x) = COMBINE (compile x) NOT
compile (ExpLTE x y) = COMBINE (compile x) (COMBINE (compile y) (COMPNATOP LTE))
compile (ExpGTE x y) = COMBINE (compile x) (COMBINE (compile y) (COMPNATOP GTE))
compile (ExpLT x y) = COMBINE (compile x) (COMBINE (compile y) (COMPNATOP LT))
compile (ExpGT x y) = COMBINE (compile x) (COMBINE (compile y) (COMPNATOP GT))
compile (ExpEqual x y) = COMBINE (compile x) (COMBINE (compile y) (EQUALOP EQUAL))
compile (ExpNotEqual x y) = COMBINE (compile x) (COMBINE (compile y) (EQUALOP NOTEQUAL))

total
evalPath: (e : Exp t) -> Val t
evalPath e = eval(e)

total
compileExecPath: (e : Exp t) -> Val t
compileExecPath e = top(exec(compile(e)) EmptyStack)
