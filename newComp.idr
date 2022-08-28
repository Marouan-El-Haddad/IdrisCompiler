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

Num (Exp Tnat) where
    (+) = ExpAddition
    (*) = ExpMultiplication
    fromInteger = ExpVal . fromInteger

Neg (Exp Tnat) where
    negate x = 0 - x
    (-) = ExpSubtraction

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
  Nil : StackData Nil
  (::) : Val x -> StackData xs -> StackData (x :: xs)

total
top : StackData (x :: xs) -> Val x
top (y :: z) = y

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
exec (PUSH x) y = x :: y
exec POP (x :: y) = y
exec ADD (x :: y :: z) = (y + x) :: z
exec SUB (x :: y :: z) = (minus y x) :: z
exec MULT (x :: y :: z) = (y * x) :: z
exec (IFTHENELSE true false) (pred :: z) = if pred then exec true z else exec false z
exec (BINBOOLOP x) (y :: z :: w) = (getOp x z y) :: w
exec NOT (x :: y) = (not x) :: y
exec (COMPNATOP x) (y :: z :: w) = (getComp x z y) :: w
exec (EQUALOP x) (y :: z :: w) = (getEqual x z y) :: w

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
compileExecPath e = top(exec(compile(e)) Nil)

-- Test evalPath against compileExecPath (arithmetic operations)
test_both_Paths_add : evalPath {t=Tnat} (2+3) = compileExecPath {t=Tnat} (2+3)
test_both_Paths_add = Refl

test_both_Paths_sub : evalPath {t=Tnat} (2-3) = compileExecPath {t=Tnat} (2-3)
test_both_Paths_sub = Refl

test_both_Paths_mul : evalPath {t=Tnat} (10*2) = compileExecPath {t=Tnat} (10*2)
test_both_Paths_mul = Refl

-- Test evalPath against compileExecPath with comparisons (TRUE)
test_both_Paths_IfThenElse_LTE_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpLTE 5 5) 50 100) = compileExecPath {t=Tnat} (ExpIfThenElse (ExpLTE 5 5) 50 100)
test_both_Paths_IfThenElse_LTE_TRUE = Refl

test_both_Paths_IfThenElse_GTE_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpGTE 5 5) 50 100) = compileExecPath {t=Tnat} (ExpIfThenElse (ExpGTE 5 5) 50 100)
test_both_Paths_IfThenElse_GTE_TRUE = Refl

test_both_Paths_IfThenElse_LT_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpLT 5 10) 50 100) = compileExecPath {t=Tnat} (ExpIfThenElse (ExpLT 5 10) 50 100)
test_both_Paths_IfThenElse_LT_TRUE = Refl

test_both_Paths_IfThenElse_GT_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpGT 11 10) 50 100) = compileExecPath {t=Tnat} (ExpIfThenElse (ExpGT 11 10) 50 100)
test_both_Paths_IfThenElse_GT_TRUE = Refl

-- Test evalPath against compileExecPath with comparisons (FALSE)
test_both_Paths_IfThenElse_LTE_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpLTE 6 5) 50 100) = compileExecPath {t=Tnat} (ExpIfThenElse (ExpLTE 6 5) 50 100)
test_both_Paths_IfThenElse_LTE_FALSE = Refl

test_both_Paths_IfThenElse_GTE_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpGTE 4 5) 50 100) = compileExecPath {t=Tnat} (ExpIfThenElse (ExpGTE 4 5) 50 100)
test_both_Paths_IfThenElse_GTE_FALSE = Refl

test_both_Paths_IfThenElse_LT_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpLT 11 10) 50 100) = compileExecPath {t=Tnat} (ExpIfThenElse (ExpLT 11 10) 50 100)
test_both_Paths_IfThenElse_LT_FALSE = Refl

test_both_Paths_IfThenElse_GT_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpGT 9 10) 50 100) = compileExecPath {t=Tnat} (ExpIfThenElse (ExpGT 9 10) 50 100)
test_both_Paths_IfThenElse_GT_FALSE = Refl

--Test EvalPath postive result
test_EvalPath_add_posRes : evalPath {t=Tnat} (2+3) = 5
test_EvalPath_add_posRes = Refl

test_EvalPath_sub_posRes : evalPath {t=Tnat} (10-3) = 7
test_EvalPath_sub_posRes = Refl

test_EvalPath_mul_posRes : evalPath {t=Tnat} (10*2) = 20
test_EvalPath_mul_posRes = Refl

--Test EvalPath neg result equal to zero
test_EvalPath_sub_ZeroIfNeg : evalPath {t=Tnat} (10-120) = 0
test_EvalPath_sub_ZeroIfNeg = Refl

{- 
--Test EvalPath negative result
test_Path_add_negRes : evalPath {t=Tnat} (-10+3) = -7
test_Path_add_negRes = Refl

test_Path_add_negRes2 : evalPath {t=Tnat} (-10+(-3)) = -13
test_Path_add_negRes2 = Refl

test_Path_sub_negRes : evalPath {t=Tnat} (2-3) = -1
test_Path_sub_negRes = Refl

test_Path_mul_negRes : evalPath {t=Tnat} (-10*2) = -20
test_Path_mul_negRes = Refl
-}

--Test EvalPath with IfThenElse using comparisons (TRUE)
test_evalPath_ifThenELse_LTE_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpLTE 5 5) 50 100) = 50
test_evalPath_ifThenELse_LTE_TRUE = Refl

test_evalPath_ifThenELse_GTE_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpGTE 5 5) 50 100) = 50
test_evalPath_ifThenELse_GTE_TRUE = Refl

test_evalPath_ifThenELse_LT_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpLT 5 10) 50 100) = 50
test_evalPath_ifThenELse_LT_TRUE = Refl

test_evalPath_ifThenELse_GT_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpGT 11 10) 50 100) = 50
test_evalPath_ifThenELse_GT_TRUE = Refl

--Test EvalPath with IfThenElse using comparisons (FALSE)
test_evalPath_ifThenELse_LTE_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpLTE 6 5) 50 100) = 100
test_evalPath_ifThenELse_LTE_FALSE = Refl

test_evalPath_ifThenELse_GTE_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpGTE 4 5) 50 100) = 100
test_evalPath_ifThenELse_GTE_FALSE = Refl

test_evalPath_ifThenELse_LT_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpLT 11 10) 50 100) = 100
test_evalPath_ifThenELse_LT_FALSE = Refl

test_evalPath_ifThenELse_GT_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpGT 9 10) 50 100) = 100
test_evalPath_ifThenELse_GT_FALSE = Refl

--Test EvalPath with IfThenElse using comparisons and NOT (TRUE)
test_evalPath_ifThenELse_LTE_NOT_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpNot (ExpLTE 10 5)) 50 100) = 50
test_evalPath_ifThenELse_LTE_NOT_TRUE = Refl

test_evalPath_ifThenELse_GTE_NOT_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpNot (ExpGTE 4 5)) 50 100) = 50
test_evalPath_ifThenELse_GTE_NOT_TRUE = Refl

test_evalPath_ifThenELse_LT_NOT_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpNot(ExpLT 11 10)) 50 100) = 50
test_evalPath_ifThenELse_LT_NOT_TRUE = Refl

test_evalPath_ifThenELse_GT_NOT_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpNot(ExpGT 4 5)) 50 100) = 50
test_evalPath_ifThenELse_GT_NOT_TRUE = Refl

--Test EvalPath with IfThenElse using comparisons and NOT (FALSE)
test_evalPath_ifThenELse_LTE_NOT_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpNot (ExpLTE 5 5)) 50 100) = 100
test_evalPath_ifThenELse_LTE_NOT_FALSE = Refl

test_evalPath_ifThenELse_GTE_NOT_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpNot (ExpGTE 5 5)) 50 100) = 100
test_evalPath_ifThenELse_GTE_NOT_FALSE = Refl

test_evalPath_ifThenELse_LT_NOT_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpNot(ExpLT 5 10)) 50 100) = 100
test_evalPath_ifThenELse_LT_NOT_FALSE = Refl

test_evalPath_ifThenELse_GT_NOT_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpNot(ExpGT 10 5)) 50 100) = 100
test_evalPath_ifThenELse_GT_NOT_FALSE = Refl

--Test EvalPath with IfThenElse using comparisons and OR (TRUE)
test_evalPath_ifThenELse_LTE_OR_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpLTE 10 5) (ExpLTE 5 5)) 50 100) = 50
test_evalPath_ifThenELse_LTE_OR_TRUE = Refl

test_evalPath_ifThenELse_GTE_OR_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpGTE 1 5) (ExpGTE 5 5)) 50 100)  = 50
test_evalPath_ifThenELse_GTE_OR_TRUE = Refl

test_evalPath_ifThenELse_LT_OR_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpLT 10 5) (ExpLT 4 5)) 50 100)  = 50
test_evalPath_ifThenELse_LT_OR_TRUE = Refl

test_evalPath_ifThenELse_GT_OR_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpGT 1 5) (ExpGT 6 5)) 50 100)  = 50
test_evalPath_ifThenELse_GT_OR_TRUE = Refl

--Test EvalPath with IfThenElse using comparisons and OR (FALSE)
test_evalPath_ifThenELse_LTE_OR_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpLTE 6 5) (ExpLTE 11 10)) 50 100) = 100
test_evalPath_ifThenELse_LTE_OR_FALSE = Refl

test_evalPath_ifThenELse_GTE_OR_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpGTE 4 5) (ExpGTE 4 5)) 50 100)  = 100
test_evalPath_ifThenELse_GTE_OR_FALSE = Refl

test_evalPath_ifThenELse_LT_OR_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpLT 6 5) (ExpLT 6 5)) 50 100)  = 100
test_evalPath_ifThenELse_LT_OR_FALSE = Refl

test_evalPath_ifThenELse_GT_OR_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpGT 1 5) (ExpGT 4 5)) 50 100)  = 100
test_evalPath_ifThenELse_GT_OR_FALSE = Refl

--Test EvalPath with IfThenElse using comparisons and AND (TRUE)
test_evalPath_ifThenELse_LTE_AND_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpLTE 5 5) (ExpLTE 10 10)) 50 100) = 50
test_evalPath_ifThenELse_LTE_AND_TRUE = Refl

test_evalPath_ifThenELse_GTE_AND_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpGTE 5 5) (ExpGTE 10 10)) 50 100)  = 50
test_evalPath_ifThenELse_GTE_AND_TRUE = Refl

test_evalPath_ifThenELse_LT_AND_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpLT 1 5) (ExpLT 4 5)) 50 100)  = 50
test_evalPath_ifThenELse_LT_AND_TRUE = Refl

test_evalPath_ifThenELse_GT_AND_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpGT 10 5) (ExpGT 6 5)) 50 100)  = 50
test_evalPath_ifThenELse_GT_AND_TRUE = Refl

--Test EvalPath with IfThenElse using comparisons and AND (FALSE)
test_evalPath_ifThenELse_LTE_AND_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpLTE 6 5) (ExpLTE 11 10)) 50 100) = 100
test_evalPath_ifThenELse_LTE_AND_FALSE = Refl

test_evalPath_ifThenELse_GTE_AND_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpGTE 4 5) (ExpGTE 9 10)) 50 100)  = 100
test_evalPath_ifThenELse_GTE_AND_FALSE = Refl

test_evalPath_ifThenELse_LT_AND_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpLT 6 5) (ExpLT 6 5)) 50 100)  = 100
test_evalPath_ifThenELse_LT_AND_FALSE = Refl

test_evalPath_ifThenELse_GT_AND_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpGT 4 5) (ExpGT 4 5)) 50 100)  = 100
test_evalPath_ifThenELse_GT_AND_FALSE = Refl

--Test EvalPath with IfThenElse using Equal (TRUE)
test_evalPath_ifThenELse_EQUAL_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpEqual 5 5) 50 100) = 50
test_evalPath_ifThenELse_EQUAL_TRUE = Refl

--Test EvalPath with IfThenElse using Equal (FALSE)
test_evalPath_ifThenELse_EQUAL_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpEqual 6 5) 50 100) = 100
test_evalPath_ifThenELse_EQUAL_FALSE = Refl

--Test EvalPath with IfThenElse using NotEqual (TRUE)
test_evalPath_ifThenELse_NOTEQUAL_TRUE : evalPath {t=Tnat} (ExpIfThenElse (ExpNotEqual 6 5) 50 100) = 50
test_evalPath_ifThenELse_NOTEQUAL_TRUE = Refl

--Test EvalPath with IfThenElse using NotEqual (FALSE)
test_evalPath_ifThenELse_NOTEQUAL_FALSE : evalPath {t=Tnat} (ExpIfThenElse (ExpNotEqual 5 5) 50 100) = 100
test_evalPath_ifThenELse_NOTEQUAL_FALSE = Refl

--Test compileExecPath postive result
test_compileExecPath_add_posRes : compileExecPath {t=Tnat} (2+3) = 5
test_compileExecPath_add_posRes = Refl

test_compileExecPath_sub_posRes : compileExecPath {t=Tnat} (10-3) = 7
test_compileExecPath_sub_posRes = Refl

test_compileExecPath_mul_posRes : compileExecPath {t=Tnat} (10*2) = 20
test_compileExecPath_mul_posRes = Refl

test_compileExecPath_sub_ZeroIfNeg : compileExecPath {t=Tnat} (10-120) = 0
test_compileExecPath_sub_ZeroIfNeg = Refl

{- 
--Test compileExecPath negative result
test_compileExecPath_add_negRes : compileExecPath {t=Tnat} (-10+3) = -7
test_compileExecPath_add_negRes = Refl

test_compileExecPath_add_negRes2 : compileExecPath {t=Tnat} (-10+(-3)) = -13
test_compileExecPath_add_negRes2 = Refl

--compileExecPath_mul_negRes : compileExecPath {t=Tnat} (-10*2) = -20
--test_compileExecPath_mul_negRes = Refl
-}

--Test compileExecPath with IfThenElse using comparisons (TRUE)
test_compileExecPath_ifThenELse_LTE_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpLTE 5 5) 50 100) = 50
test_compileExecPath_ifThenELse_LTE_TRUE = Refl

test_compileExecPath_ifThenELse_GTE_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpGTE 5 5) 50 100) = 50
test_compileExecPath_ifThenELse_GTE_TRUE = Refl

test_compileExecPath_ifThenELse_LT_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpLT 5 10) 50 100) = 50
test_compileExecPath_ifThenELse_LT_TRUE = Refl

test_compileExecPath_ifThenELse_GT_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpGT 11 10) 50 100) = 50
test_compileExecPath_ifThenELse_GT_TRUE = Refl

--Test compileExecPath with IfThenElse using comparisons (FALSE)
test_compileExecPath_ifThenELse_LTE_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpLTE 6 5) 50 100) = 100
test_compileExecPath_ifThenELse_LTE_FALSE = Refl

test_compileExecPath_ifThenELse_GTE_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpGTE 4 5) 50 100) = 100
test_compileExecPath_ifThenELse_GTE_FALSE = Refl

test_compileExecPath_ifThenELse_LT_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpLT 11 10) 50 100) = 100
test_compileExecPath_ifThenELse_LT_FALSE = Refl

test_compileExecPath_ifThenELse_GT_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpGT 9 10) 50 100) = 100
test_compileExecPath_ifThenELse_GT_FALSE = Refl

--Test compileExecPath with IfThenElse using comparisons and NOT (TRUE)
test_compileExecPath_ifThenELse_LTE_NOT_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpNot (ExpLTE 10 5)) 50 100) = 50
test_compileExecPath_ifThenELse_LTE_NOT_TRUE = Refl

test_compileExecPath_ifThenELse_GTE_NOT_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpNot (ExpGTE 4 5)) 50 100) = 50
test_compileExecPath_ifThenELse_GTE_NOT_TRUE = Refl

test_compileExecPath_ifThenELse_LT_NOT_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpNot(ExpLT 11 10)) 50 100) = 50
test_compileExecPath_ifThenELse_LT_NOT_TRUE = Refl

test_compileExecPath_ifThenELse_GT_NOT_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpNot(ExpGT 4 5)) 50 100) = 50
test_compileExecPath_ifThenELse_GT_NOT_TRUE = Refl

--Test compileExecPath with IfThenElse using comparisons and NOT (FALSE)
test_compileExecPath_ifThenELse_LTE_NOT_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpNot (ExpLTE 5 5)) 50 100) = 100
test_compileExecPath_ifThenELse_LTE_NOT_FALSE = Refl

test_compileExecPath_ifThenELse_GTE_NOT_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpNot (ExpGTE 5 5)) 50 100) = 100
test_compileExecPath_ifThenELse_GTE_NOT_FALSE = Refl

test_compileExecPath_ifThenELse_LT_NOT_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpNot(ExpLT 5 10)) 50 100) = 100
test_compileExecPath_ifThenELse_LT_NOT_FALSE = Refl

test_compileExecPath_ifThenELse_GT_NOT_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpNot(ExpGT 10 5)) 50 100) = 100
test_compileExecPath_ifThenELse_GT_NOT_FALSE = Refl

--Test compileExecPath with IfThenElse using comparisons and OR (TRUE)
test_compileExecPath_ifThenELse_LTE_OR_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpLTE 10 5) (ExpLTE 5 5)) 50 100) = 50
test_compileExecPath_ifThenELse_LTE_OR_TRUE = Refl

test_compileExecPath_ifThenELse_GTE_OR_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpGTE 1 5) (ExpGTE 5 5)) 50 100)  = 50
test_compileExecPath_ifThenELse_GTE_OR_TRUE = Refl

test_compileExecPath_ifThenELse_LT_OR_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpLT 10 5) (ExpLT 4 5)) 50 100)  = 50
test_compileExecPath_ifThenELse_LT_OR_TRUE = Refl

test_compileExecPath_ifThenELse_GT_OR_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpGT 1 5) (ExpGT 6 5)) 50 100)  = 50
test_compileExecPath_ifThenELse_GT_OR_TRUE = Refl

--Test compileExecPath with IfThenElse using comparisons and OR (FALSE)
test_compileExecPath_ifThenELse_LTE_OR_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpLTE 6 5) (ExpLTE 11 10)) 50 100) = 100
test_compileExecPath_ifThenELse_LTE_OR_FALSE = Refl

test_compileExecPath_ifThenELse_GTE_OR_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpGTE 4 5) (ExpGTE 4 5)) 50 100)  = 100
test_compileExecPath_ifThenELse_GTE_OR_FALSE = Refl

test_compileExecPath_ifThenELse_LT_OR_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpLT 6 5) (ExpLT 6 5)) 50 100)  = 100
test_compileExecPath_ifThenELse_LT_OR_FALSE = Refl

test_compileExecPath_ifThenELse_GT_OR_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpOr (ExpGT 1 5) (ExpGT 4 5)) 50 100)  = 100
test_compileExecPath_ifThenELse_GT_OR_FALSE = Refl

--Test compileExecPath with IfThenElse using comparisons and AND (TRUE)
test_compileExecPath_ifThenELse_LTE_AND_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpLTE 5 5) (ExpLTE 10 10)) 50 100) = 50
test_compileExecPath_ifThenELse_LTE_AND_TRUE = Refl

test_compileExecPath_ifThenELse_GTE_AND_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpGTE 5 5) (ExpGTE 10 10)) 50 100)  = 50
test_compileExecPath_ifThenELse_GTE_AND_TRUE = Refl

test_compileExecPath_ifThenELse_LT_AND_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpLT 1 5) (ExpLT 4 5)) 50 100)  = 50
test_compileExecPath_ifThenELse_LT_AND_TRUE = Refl

test_compileExecPath_ifThenELse_GT_AND_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpGT 10 5) (ExpGT 6 5)) 50 100)  = 50
test_compileExecPath_ifThenELse_GT_AND_TRUE = Refl

--Test compileExecPath with IfThenElse using comparisons and AND (FALSE)
test_compileExecPath_ifThenELse_LTE_AND_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpLTE 6 5) (ExpLTE 11 10)) 50 100) = 100
test_compileExecPath_ifThenELse_LTE_AND_FALSE = Refl

test_compileExecPath_ifThenELse_GTE_AND_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpGTE 4 5) (ExpGTE 9 10)) 50 100)  = 100
test_compileExecPath_ifThenELse_GTE_AND_FALSE = Refl

test_compileExecPath_ifThenELse_LT_AND_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpLT 6 5) (ExpLT 6 5)) 50 100)  = 100
test_compileExecPath_ifThenELse_LT_AND_FALSE = Refl

test_compileExecPath_ifThenELse_GT_AND_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpAnd (ExpGT 4 5) (ExpGT 4 5)) 50 100)  = 100
test_compileExecPath_ifThenELse_GT_AND_FALSE = Refl

--Test EvalPath with IfThenElse using NotEqual (TRUE)
test_compileExecPath_ifThenELse_NOTEQUAL_TRUE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpNotEqual 6 5) 50 100) = 50
test_compileExecPath_ifThenELse_NOTEQUAL_TRUE = Refl

--Test EvalPath with IfThenElse using NotEqual (FALSE)
test_compileExecPath_ifThenELse_NOTEQUAL_FALSE : compileExecPath {t=Tnat} (ExpIfThenElse (ExpNotEqual 5 5) 50 100) = 100
test_compileExecPath_ifThenELse_NOTEQUAL_FALSE = Refl
