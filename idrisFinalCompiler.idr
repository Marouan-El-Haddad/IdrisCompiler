import Data.Vect

data TyExp
    = Tint
    | Tbool

Val : TyExp -> Type
Val Tint = Int
Val Tbool = Bool

data HasTypeVar : (i : Fin n) -> Vect n TyExp -> TyExp -> Type where
    StopVar : HasTypeVar FZ (t :: cntxt) t 
    PopVar  : HasTypeVar k cntxt t -> HasTypeVar (FS k) (u :: cntxt) t

data HasTypeFunc : (i : Fin n) -> Vect n (TyExp, TyExp) -> (TyExp, TyExp) -> Type where
    StopFunc : HasTypeFunc FZ ((t,s) :: cntxt) (t, s)
    PopFunc : HasTypeFunc k cntxt (t,s) -> HasTypeFunc (FS k) ((u,v) :: cntxt) (t, s)

data Exp : (vEnv: Vect n TyExp) -> (fEnv: Vect m (TyExp, TyExp)) -> TyExp -> Type where
  ExpVar : HasTypeVar i vEnv t -> Exp vEnv fEnv t
  ExpVal : (x: Int) -> Exp cntxt fEnv Tint
  ExpAddition : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpSubtraction : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpMultiplication : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpIfThenElse : Exp vEnv fEnv Tbool -> Exp vEnv fEnv a -> Exp vEnv fEnv a -> Exp vEnv fEnv a
  ExpOr: Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool
  ExpAnd: Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool
  ExpNot: Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool
  ExpLTE: Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpGTE: Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpLT: Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpGT: Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpEqual: Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpNotEqual: Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpFuncCall: HasTypeFunc i fEnv (t,s) -> Exp vEnv fEnv t-> Exp vEnv fEnv s

record FunDecl where
  constructor MkFunDecl
  var_type: TyExp
  return_type: TyExp
  body: Exp [var_type] [(var_type, return_type)] return_type

record OpenProgram where
  constructor MkOpenProgram 
  funDecl: FunDecl
  return_type: TyExp
  arg_env : TyExp
  mainExp: Exp [arg_env] [(funDecl.var_type, funDecl.return_type)] return_type

data Env : Vect n TyExp -> Type where
    Nil  : Env Nil
    (::) : Val a -> Env cntxt -> Env (a :: cntxt)

lookupVar : HasTypeVar i cntxt t -> Env cntxt -> Val t
lookupVar StopVar (x :: xs) = x
lookupVar (PopVar k) (x :: xs) = lookupVar k xs

evalOpenProg : Env cntxt -> (x: OpenProgram) -> Val x.return_type
evalOpenProg env (MkOpenProgram funDecl return_type arg_env (ExpVar x)) = ?hole1 --lookupVar x env 
evalOpenProg env (MkOpenProgram funDecl Tint arg_env (ExpVal x)) = x
evalOpenProg env (MkOpenProgram funDecl Tint arg_env (ExpAddition x y)) = ?hole --(evalOpenProg env (MkOpenProgram funDecl Tint arg_env x)) + (evalOpenProg env (MkOpenProgram funDecl Tint arg_env y))
evalOpenProg env (MkOpenProgram funDecl Tint arg_env (ExpSubtraction x y)) = (evalOpenProg env (MkOpenProgram funDecl Tint arg_env x)) - (evalOpenProg env (MkOpenProgram funDecl Tint arg_env y)) 
evalOpenProg env (MkOpenProgram funDecl Tint arg_env (ExpMultiplication x y)) = (evalOpenProg env (MkOpenProgram funDecl Tint arg_env x)) * (evalOpenProg env (MkOpenProgram funDecl Tint arg_env y))
evalOpenProg env (MkOpenProgram funDecl return_type arg_env (ExpIfThenElse x y z)) = if (evalOpenProg env (MkOpenProgram funDecl Tbool arg_env x)) 
                                                                                     then (evalOpenProg env (MkOpenProgram funDecl return_type arg_env y))
                                                                                     else (evalOpenProg env (MkOpenProgram funDecl return_type arg_env z))
evalOpenProg env (MkOpenProgram funDecl Tbool arg_env (ExpOr x y)) = (evalOpenProg env (MkOpenProgram funDecl Tbool arg_env x)) || (evalOpenProg env (MkOpenProgram funDecl Tbool arg_env y))
evalOpenProg env (MkOpenProgram funDecl Tbool arg_env (ExpAnd x y)) = (evalOpenProg env (MkOpenProgram funDecl Tbool arg_env x)) && (evalOpenProg env (MkOpenProgram funDecl Tbool arg_env y))
evalOpenProg env (MkOpenProgram funDecl Tbool arg_env (ExpNot x)) = not (evalOpenProg env (MkOpenProgram funDecl Tbool arg_env x))
evalOpenProg env (MkOpenProgram funDecl Tbool arg_env (ExpLTE x y)) = (evalOpenProg env (MkOpenProgram funDecl Tint arg_env x)) <= (evalOpenProg env (MkOpenProgram funDecl Tint arg_env y))
evalOpenProg env (MkOpenProgram funDecl Tbool arg_env (ExpGTE x y)) = (evalOpenProg env (MkOpenProgram funDecl Tint arg_env x)) >= (evalOpenProg env (MkOpenProgram funDecl Tint arg_env y))
evalOpenProg env (MkOpenProgram funDecl Tbool arg_env (ExpLT x y)) = (evalOpenProg env (MkOpenProgram funDecl Tint arg_env x)) < (evalOpenProg env (MkOpenProgram funDecl Tint arg_env y))
evalOpenProg env (MkOpenProgram funDecl Tbool arg_env (ExpGT x y)) = (evalOpenProg env (MkOpenProgram funDecl Tint arg_env x)) > (evalOpenProg env (MkOpenProgram funDecl Tint arg_env y))
evalOpenProg env (MkOpenProgram funDecl Tbool arg_env (ExpEqual x y)) = (evalOpenProg env (MkOpenProgram funDecl Tint arg_env x)) == (evalOpenProg env (MkOpenProgram funDecl Tint arg_env y))
evalOpenProg env (MkOpenProgram funDecl Tbool arg_env (ExpNotEqual x y)) = (evalOpenProg env (MkOpenProgram funDecl Tint arg_env x)) /= (evalOpenProg env (MkOpenProgram funDecl Tint arg_env y))
evalOpenProg env (MkOpenProgram (MkFunDecl var_type x body) return_type arg_env (ExpFuncCall f s)) = ?hole2_0 --evalOpenProg env f (evalOpenProg env s)
--evalOpenProg env (MkOpenProgram funDecl return_type arg_env (ExpFuncCall f s)) = (evalOpenProg env (MkOpenProgram funDecl return_type arg_env f (evalOpenProg env (MkOpenProgram funDecl return_type arg_env s))))

record Program where
  constructor MkProgram
  funDecl: FunDecl
  return_type: TyExp
  mainExp: Exp [] [(funDecl.var_type, funDecl.return_type)] return_type
--f(x) = x + 2
--f(10) = 12

evalProg : Env cntxt -> (x: Program) ->  Val x.return_type
evalProg env (MkProgram funDecl return_type (ExpVar x)) = ?evalProg_rhs_1
evalProg env (MkProgram funDecl Tint (ExpVal x)) = x
evalProg env (MkProgram funDecl Tint (ExpAddition x y)) = (evalProg env (MkProgram funDecl Tint x)) + (evalProg env (MkProgram funDecl Tint y))
evalProg env (MkProgram funDecl Tint (ExpSubtraction x y)) = (evalProg env (MkProgram funDecl Tint x)) - (evalProg env (MkProgram funDecl Tint y))
evalProg env (MkProgram funDecl Tint (ExpMultiplication x y)) = (evalProg env (MkProgram funDecl Tint x)) * (evalProg env (MkProgram funDecl Tint y))
evalProg env (MkProgram funDecl return_type (ExpIfThenElse x y z)) = if (evalProg env (MkProgram funDecl Tbool x)) 
                                                                                     then (evalProg env (MkProgram funDecl return_type y))
                                                                                     else (evalProg env (MkProgram funDecl return_type z))
evalProg env (MkProgram funDecl Tbool (ExpOr x y)) = (evalProg env (MkProgram funDecl Tbool x)) || (evalProg env (MkProgram funDecl Tbool y))
evalProg env (MkProgram funDecl Tbool (ExpAnd x y)) = (evalProg env (MkProgram funDecl Tbool x)) && (evalProg env (MkProgram funDecl Tbool y))
evalProg env (MkProgram funDecl Tbool (ExpNot x)) = not (evalProg env (MkProgram funDecl Tbool x))
evalProg env (MkProgram funDecl Tbool (ExpLTE x y)) = (evalProg env (MkProgram funDecl Tint x)) <= (evalProg env (MkProgram funDecl Tint y))
evalProg env (MkProgram funDecl Tbool (ExpGTE x y)) = (evalProg env (MkProgram funDecl Tint x)) >= (evalProg env (MkProgram funDecl Tint y))
evalProg env (MkProgram funDecl Tbool (ExpLT x y)) = (evalProg env (MkProgram funDecl Tint x)) < (evalProg env (MkProgram funDecl Tint y))
evalProg env (MkProgram funDecl Tbool (ExpGT x y)) = (evalProg env (MkProgram funDecl Tint x)) > (evalProg env (MkProgram funDecl Tint y))
evalProg env (MkProgram funDecl Tbool (ExpEqual x y)) = (evalProg env (MkProgram funDecl Tint x)) == (evalProg env (MkProgram funDecl Tint y))
evalProg env (MkProgram funDecl Tbool (ExpNotEqual x y)) = (evalProg env (MkProgram funDecl Tint x)) /= (evalProg env (MkProgram funDecl Tint y))
evalProg env (MkProgram funDecl return_type (ExpFuncCall x y)) = ?evalProg_rhs_16
