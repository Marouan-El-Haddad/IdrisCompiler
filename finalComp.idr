import Data.Vect
%default total

data TyExp
    = Tint
    | Tbool

Val : TyExp -> Type
Val Tint = Int
Val Tbool = Bool

data HasTypeVar : (i : Fin n) -> Vect n TyExp -> TyExp -> Type where
    StopVar : HasTypeVar FZ (t :: ctxt) t
    PopVar  : HasTypeVar k ctxt t -> HasTypeVar (FS k) (u :: ctxt) t

data HasTypeFunc : (i : Fin n) -> Vect n (TyExp, TyExp) -> (TyExp, TyExp) -> Type where
    StopFunc : HasTypeFunc FZ ((t,s) :: ctxt) (t, s)
    PopFunc : HasTypeFunc k ctxt (t,s) -> HasTypeFunc (FS k) ((u,v) :: ctxt) (t, s)
 
data Exp : (vEnv: Vect n TyExp) -> (fEnv: Vect m (TyExp, TyExp)) -> TyExp -> Type where
  ExpVar : HasTypeVar i vEnv t -> Exp vEnv fEnv t
  ExpVal : (x: Integer) -> Exp cntxt fEnv tInt
  ExpAddition : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpFuncCall: HasTypeFunc i fEnv (t,s) -> Exp vEnv fEnv t-> Exp vEnv fEnv s

testFuncCall : Exp [Tbool] [(Tbool, Tbool)] Tbool
testFuncCall = ExpFuncCall StopFunc (ExpVar StopVar)

{-
different note: in PopFunc, 
why do you have s repeated in HasTypeFunc (FS k) ((u,s) :: ctxt) (t, s) 
rather than using HasTypeFunc (FS k) ((u,v) :: ctxt) (t, s)
-}

--x
myExp : Exp [Tint] [] Tint
myExp = ExpVar StopVar

--x + 2
myExp2 : Exp [Tint] [] Tint
myExp2 = ExpAddition (ExpVar StopVar) (ExpVal 2)

--x + y
myExp3 : Exp [Tint, Tint] [] Tint
myExp3 = ExpAddition (ExpVar StopVar) (ExpVar (PopVar StopVar))

-- x + (Int -> Int)
myExp4 : Exp [Tint] [(Tint, Tint)] Tint
myExp4 = ?hole

{- 
record FuncDef where 
Afhængig record FuncDef Skal kende fEnv, og have argType som input og RetType output 
Body skal bruge Variable
  constructor MkFuncDef
  body: Exp return_type
  
--f(x) = x+2
--MkFuncDef (Just "f") "x" Tint Tint (ExpPlus (ExpVar "x") (ExpVal 2))

data FullProgram : 

{- 
FuncEnv: Type --afhænge af fEnv
FuncEnv = List FuncDef

-- data FuncDef : Vect n TyExp -> TyExp -> TyExp -> Type where
    -- funcDef : (func_name: String) -> (arg_name: String) -> (arg_type: TyExp) -> (func_body: Exp ctxt t) -> FuncDef ctxt t t

data Env2 : Vect n TyExp -> Type where
    Nil  : Env2 Nil
    (::) : Val a -> Env2 ctxt -> Env2 (a :: ctxt)

Env : Type
Env = List (String, (t : TyExp ** Val t))

lookup : String -> Env -> Maybe (t : TyExp ** Val t)
lookup str [] = Nothing
lookup str (x :: xs) = case x of
  (str', val) => if str == str' then Just val else lookup str xs


 {-
 data TyExp
    = Tint
    | Tbool
    | Tpair TyExp TyExp

Val : TyExp -> Type
Val Tint = Int
Val Tbool = Bool
Val (Tpair t u) = Pair (Val t) (Val u)

data HasTypeVar : (i : Fin n) -> Vect n TyExp -> TyExp -> Type where
    StopVar : HasTypeVar FZ (t :: ctxt) t
    PopVar  : HasTypeVar k ctxt t -> HasTypeVar (FS k) (u :: ctxt) t

data HasTypeFunc : (i : Fin n) -> Vect m (TyExp, TyExp) -> (TyExp, TyExp) -> Type where --HERE
    StopFunc : HasTypeFunc FZ  ((t,s) :: ctxt) (t, s)
    PopFunc : HasTypeFunc k ctxt (t,s) -> HasTypeFunc (FS k) ((u,v) :: ctxt) (t, s)
 
data Exp : (vEnv: Vect n TyExp) -> (fEnv: Vect m (TyExp, TyExp)) -> TyExp -> Type where
  ExpVar : HasTypeVar i vEnv t -> Exp vEnv fEnv t
  ExpVal : (x: Integer) -> Exp cntxt fEnv tInt
  ExpTuple : HasTypeVar i vEnv t -> HasTypeVar j vEnv u -> Exp vEnv fEnv (Tpair t u)
  ExpFirst : HasTypeVar i vEnv (Tpair t u) -> Exp vEnv fEnv t
  ExpSecond : HasTypeVar i vEnv (Tpair t u) -> Exp vEnv fEnv u
  ExpAddition : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpFuncCall: HasTypeFunc i fEnv (t,s) -> Exp vEnv fEnv t-> Exp vEnv fEnv s --HERE

testFuncCall : Exp [Tbool] [(Tbool, Tbool)] Tbool
testFuncCall = ExpFuncCall StopFunc (ExpVar StopVar)
 
  -}
