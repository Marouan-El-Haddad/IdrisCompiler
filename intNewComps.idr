import Data.Vect
%default total

--The Enumerated data type TyExp is defined by giving the valid values for that type. 
--The data keyword introduces a new data type, ie. the declaration, and then the next is the name of type constructor (TyExp in this case). 
--Lastly the names of the data constructors are listed (Tint and Tbool in this case), each separated by the vertical bar "|", indicating a choice
--The enumerated type syntax is
--a shorthand version of the data <name> where <constructors> form, 
--where each enumerated constructor name defines a type constructor of type <name>
--Although theoretically possible, it is not advisable to operate on Idris types directly here. 
--We'd rather use a closed custom data type describing the types of columns I understand. 
--In a first try, I only support some Idris primitives
data TyExp
    = Tint
    | Tbool

--I then use the data type TyExp, to define a function Val.
--First line is a function type with TyExp as the input and a Type as output. 
--The next lines are the definition of the function. 
--A Val with Tint as argument will evaluate to an Int, and a Val with Tbool will evaluate to a Bool.
Val : TyExp -> Type
Val Tint = Int
Val Tbool = Bool

--Dependent data type
--This is a data type that is computed from another value. The exact type is thus calculated from the Vectors Length.
--By using a Vect for the variable, with its size as part of the type, the type system can
--ensure that any access of the variable by index will be within bounds, because you have to
--show that the index has the same upper bound as the length of the Vect
--I use a nameless representation for variables — they are de Bruijn indexed. 
--Variables are represented by a proof of their membership in the cntxt, 
--HasType i cntxt T, which is a proof that variable i in cntxt cntxt has type T. This is defined as follows:
--I can treat Stop as a proof that the most recently defined variable is well-typed, 
--and Pop n as a proof that, if the nth most recently defined variable is well-typed, 
--so is the n+1th. In practice, this means I use Stop to refer to the most recently defined variable, 
--Pop Stop to refer to the next, and so on, via the Var constructor
--So, in an expression \x. \y. x y, the variable x would have a de Bruijn index of 1, 
--represented as Pop Stop, and y 0, represented as Stop. 
--I find these by counting the number of lambdas between the definition and the use.
data HasTypeVar : (i : Fin n) -> Vect n TyExp -> TyExp -> Type where
    StopVar : HasTypeVar FZ (t :: cntxt) t 
    PopVar  : HasTypeVar k cntxt t -> HasTypeVar (FS k) (u :: cntxt) t

data HasTypeFunc : (i : Fin n) -> Vect n (TyExp, TyExp) -> (TyExp, TyExp) -> Type where
    StopFunc : HasTypeFunc FZ ((t,s) :: cntxt) (t, s)
    PopFunc : HasTypeFunc k cntxt (t,s) -> HasTypeFunc (FS k) ((u,v) :: cntxt) (t, s)

--I am relying on a venv/fenv being part of the construction of a functiondef 
--which means I can't do the typechecking after and, importantly, and I can't separate concerns
data Exp : (vEnv: Vect n TyExp) -> (fEnv: Vect m (TyExp, TyExp)) -> TyExp -> Type where
  ExpVar : HasTypeVar i vEnv t -> Exp vEnv fEnv t
  ExpVal : (x: Integer) -> Exp cntxt fEnv Tint
  ExpAddition : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpSubtraction : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpMultiplication : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpIfThenElse : Exp vENv fEnv Tbool -> Lazy (Exp vEnv fEnv a) -> Lazy (Exp vEnv fEnv a) -> Exp vEnv fEnv a
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

{- 
data Exp' : (vEnv: Vect n TyExp) -> (fEnv: Vect m (TyExp, TyExp)) -> TyExp -> Type where
  ExpVar' : HasTypeVar i vEnv t -> Exp' vEnv fEnv t
  ExpVal' : (x: Integer) -> Exp' cntxt fEnv Tint
  ExpAddition' : Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tint
  ExpSubtraction' : Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tint
  ExpMultiplication' : Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tint
  ExpIfThenElse' : Exp' vENv fEnv Tbool -> Lazy (Exp vEnv fEnv a) -> Lazy (Exp vEnv fEnv a) -> Exp' vEnv fEnv a
  ExpOr': Exp' vEnv fEnv Tbool -> Exp' vEnv fEnv Tbool -> Exp' vEnv fEnv Tbool
  ExpAnd': Exp' vEnv fEnv Tbool -> Exp' vEnv fEnv Tbool -> Exp' vEnv fEnv Tbool
  ExpNot': Exp' vEnv fEnv Tbool -> Exp' vEnv fEnv Tbool
  ExpLTE': Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tbool
  ExpGTE': Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tbool
  ExpLT': Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tbool
  ExpGT': Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tbool
  ExpEqual': Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tbool
  ExpNotEqual': Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tint -> Exp' vEnv fEnv Tbool
  ExpFuncCall': HasTypeFunc i fEnv (t,s) -> Exp' vEnv fEnv t-> Exp' vEnv fEnv s
-}

--xl
myExp : Exp [Tint] [] Tint
myExp = ExpVar StopVar

--x + 2
myExp2 : Exp [Tint] [] Tint
myExp2 = ExpAddition (ExpVar StopVar) (ExpVal 2)

--x + y
myExp3 : Exp [Tint, Tint] [] Tint
myExp3 = ExpAddition (ExpVar StopVar) (ExpVar (PopVar StopVar))

-- (x:Tint) (Int -> Int)
myExp4 : Exp [Tint] [(Tint, Tint)] Tint
myExp4 = ExpFuncCall StopFunc (ExpVar StopVar) 

myExp5 : Exp [Tbool] [(Tbool, Tbool)] Tbool
myExp5 = ExpFuncCall StopFunc (ExpVar StopVar)

{- 
record Program where
  constructor MkProgram
  var_type: TyExp
  return_type: TyExp
  body: Exp [var_type] [(var_type, return_type)] return_type
  mainExp: Exp [var_type] [(var_type, return_type)] return_type -> Exp [var_type] [] return_type -> Val return_type

record Program' where
  constructor MkProgram'
  var_type: TyExp
  return_type: TyExp
  body: Exp [var_type] [(var_type, return_type)] return_type
  mainExp: Exp [var_type] [(var_type, return_type)] return_type -> Exp [var_type] [] return_type -> Exp [var_type] [] return_type


record Program where
  constructor MkProgram
  var_type: TyExp
  return_type: TyExp
  body: Exp [var_type] [(var_type, return_type)] return_type
  mainExp : Exp [] [(var_type, return_type)] return_type

-}
record FunDecl where
  constructor MkFunDecl
  var_type: TyExp
  return_type: TyExp
  body: Exp [var_type] [(var_type, return_type)] return_type

--mainExp is an expression with no free expression variables, and one free function variable,
-- which I can set to the previously defined function when I actually run the program
--mainExp field has one free function variable 
--that can be instantiated to the function defined in the funDecl field when I run the program. 
--Now my function can return an int while the main expression returns a bool, or whatever I like. 
--This also sets me up to more easily generalize to a list of function declarations

record Program where
  constructor MkProgram
  funDecl: FunDecl
  return_type: TyExp
  mainExp: Exp [] [(funDecl.var_type, funDecl.return_type)] return_type
--f(x) = x + 2
--f(14)

record OpenProgram where
  constructor MkOpenProgram
  funDecl: FunDecl
  return_type: TyExp
  arg_env : TyExp
  mainExp: Exp [arg_env] [(funDecl.var_type, funDecl.return_type)] return_type
--f(x) = x + 2
--y + f(14)


--FullProg: Type
--FullProg = List FunDecl

--  mainExp: body = ExpFuncCall StopFunc (ExpVar StopVar)
--myProgram : Program
--myProgram = MkProgram ?hole ?hole2 ?hole3 ?hole4

  --mainExp: Create a field mainExp that can represent f(14)+2
  --Create a field mainExp that can represent f(14)+2 and return the result with the function eval 
  --tirsdag kl 10 møde

data EnvArg : Vect n TyExp -> Type where
    Nil  : EnvArg Nil
    (::) : Val a -> EnvArg cntxt -> EnvArg (a :: cntxt)

lookup : HasTypeVar i ctxt t -> EnvArg ctxt -> Val t
lookup StopVar (x :: xs) = x
lookup (PopVar k) (x :: xs) = lookup k xs

evalFunc : EnvArg cntxt -> (x: Program) ->  Val x.return_type
evalFunc envArg (MkProgram funDecl return_type (ExpVar x)) = ?evalFunc_rhs_1
evalFunc envArg (MkProgram funDecl Tint (ExpVal x)) = ?evalFunc_rhs_2
evalFunc envArg (MkProgram funDecl Tint (ExpAddition x y)) = ?evalFunc_rhs_3
evalFunc envArg (MkProgram funDecl Tint (ExpSubtraction x y)) = ?evalFunc_rhs_4
evalFunc envArg (MkProgram funDecl Tint (ExpMultiplication x y)) = ?evalFunc_rhs_5
evalFunc envArg (MkProgram funDecl return_type (ExpIfThenElse x y z)) = ?evalFunc_rhs_6
evalFunc envArg (MkProgram funDecl Tbool (ExpOr x y)) = ?evalFunc_rhs_7
evalFunc envArg (MkProgram funDecl Tbool (ExpAnd x y)) = ?evalFunc_rhs_8
evalFunc envArg (MkProgram funDecl Tbool (ExpNot x)) = ?evalFunc_rhs_9
evalFunc envArg (MkProgram funDecl Tbool (ExpLTE x y)) = ?evalFunc_rhs_10
evalFunc envArg (MkProgram funDecl Tbool (ExpGTE x y)) = ?evalFunc_rhs_11
evalFunc envArg (MkProgram funDecl Tbool (ExpLT x y)) = ?evalFunc_rhs_12
evalFunc envArg (MkProgram funDecl Tbool (ExpGT x y)) = ?evalFunc_rhs_13
evalFunc envArg (MkProgram funDecl Tbool (ExpEqual x y)) = ?evalFunc_rhs_14
evalFunc envArg (MkProgram funDecl Tbool (ExpNotEqual x y)) = ?evalFunc_rhs_15
evalFunc envArg (MkProgram funDecl return_type (ExpFuncCall x y)) = ?evalFunc_rhs_16


evalOpenFunc : EnvArg cntxt -> (x: OpenProgram) -> Val x.return_type
evalOpenFunc envArg (MkOpenProgram funDecl return_type arg_env (ExpVar x)) = ?evalOpenFunc_rhs_1
evalOpenFunc envArg (MkOpenProgram funDecl Tint arg_env (ExpVal x)) = ?evalOpenFunc_rhs_2
evalOpenFunc envArg (MkOpenProgram funDecl Tint arg_env (ExpAddition x y)) = ?evalOpenFunc_rhs_3
evalOpenFunc envArg (MkOpenProgram funDecl Tint arg_env (ExpSubtraction x y)) = ?evalOpenFunc_rhs_4
evalOpenFunc envArg (MkOpenProgram funDecl Tint arg_env (ExpMultiplication x y)) = ?evalOpenFunc_rhs_5
evalOpenFunc envArg (MkOpenProgram funDecl return_type arg_env (ExpIfThenElse x y z)) = ?evalOpenFunc_rhs_6
evalOpenFunc envArg (MkOpenProgram funDecl Tbool arg_env (ExpOr x y)) = ?evalOpenFunc_rhs_7
evalOpenFunc envArg (MkOpenProgram funDecl Tbool arg_env (ExpAnd x y)) = ?evalOpenFunc_rhs_8
evalOpenFunc envArg (MkOpenProgram funDecl Tbool arg_env (ExpNot x)) = ?evalOpenFunc_rhs_9
evalOpenFunc envArg (MkOpenProgram funDecl Tbool arg_env (ExpLTE x y)) = ?evalOpenFunc_rhs_10
evalOpenFunc envArg (MkOpenProgram funDecl Tbool arg_env (ExpGTE x y)) = ?evalOpenFunc_rhs_11
evalOpenFunc envArg (MkOpenProgram funDecl Tbool arg_env (ExpLT x y)) = ?evalOpenFunc_rhs_12
evalOpenFunc envArg (MkOpenProgram funDecl Tbool arg_env (ExpGT x y)) = ?evalOpenFunc_rhs_13
evalOpenFunc envArg (MkOpenProgram funDecl Tbool arg_env (ExpEqual x y)) = ?evalOpenFunc_rhs_14
evalOpenFunc envArg (MkOpenProgram funDecl Tbool arg_env (ExpNotEqual x y)) = ?evalOpenFunc_rhs_15
evalOpenFunc envArg (MkOpenProgram funDecl return_type arg_env (ExpFuncCall x y)) = ?evalOpenFunc_rhs_16



--skal udvides til at bruge Env og program  

{-
Env : Type
Env = List (String, (t : TyExp ** Val t))

lookup : String -> Env -> Maybe (t : TyExp ** Val t)
lookup str [] = Nothing
lookup str (x :: xs) = case x of
  (str', val) => if str == str' then Just val else lookup str xs
f
  var_type: TyExp
  return_type: TyExp
  body: Exp [var_type] [(var_type, return_type)] return_type
 -}
-- f(x) = if x < 2 then 1 else x * f(x-1)
-- can't do f(x) = g(f(y-2))

--The core thing that I am doing with these definitions is relying on a venv/fenv being part of the construction of a functiondef 
-- which means I can't do the typechecking after and, importantly, you I can't separate concerns
--return_type is implicit because of premature design-optimization: 
--the body is an expression with this return_type,
--users of MkFuncDef will supply the body expression
--(as opposed to partially-applying the data constructor)
--So the return_type should be unambiguously inferred from the body expression.

--check_fn_def : FuncDef -> (vEnv: Vect n TyExp) -> (fEnv: Vect m (TyExp, TyExp)) -> (fEnv: Vect m (TyExp, TyExp)) -> Type
--check_fn_def (MkFuncDef function body) vEnv fEnv xs = ?check_fn_def_rhs_0


{- 
record FuncDef a b c where 
  constructor MkFuncDef
  function: FuncHeader
  body: Vect ns (Exp a b c)
--MkFuncDef "f" "x" [Tint] [(Tint, Tint)] (ExpAddition (ExpVar StopVar) (ExpVal 2))
--"f" ("x": [Int]) : [Int -> Int] = Exp ExpAddition (ExpVar StopVar) (ExpVal 2)
--f(x) = x + 2 



record FullProgram where
  constructor MkFullProgram
  func_defs: Vect ms FuncDef
  ret_type: TyExp
  main: Exp [] [] ret_type

--FullProg: Type
--FullProg = List FuncDef

--myProgram : FullProgram
--myProgram = MkFullProgram [MkFuncDef "f" "x" [Tint] [(Tint, Tint)] Tint (ExpAddition (ExpVar StopVar) (ExpVal 2))] Tint (ExpFuncCall StopFunc (ExpVal 2))

record FuncDef where
  constructor MkFuncDef
  func_name: String
  arg_name: String
  arg_type: TyExp
  {return_type: TyExp}
  body: Exp return_type
 
record FullProgram where -- user function fEnv
  constructor MkFullProgram
  fEnv: Vect m (TyExp, TyExp)
  func_defs: List FuncDef -- skal ikke være tom, skal afhænge af fEnv så jeg ikke får forkerte typer
  main: Exp [] [] Tint 

  fEnv: [(Tint, Tint), (Tbool, Tint)]
  funDef: []

-- fEnv (f: Int -> Int)
-- FunDef (f(x) = g(x)+4) (skal bruge Exp)
-- Main expression: evaluer FuncDef f(g(2)) 
--Tager List of FuncDef, funcCall

ChoiceVal : Bool -> Type -> Type -> Type
ChoiceVal True a b = a
ChoiceVal False a b = b

record FunkyEither (a, b : Type) where
  constructor MkFunkyEither
  choice : Bool
  value : ChoiceVal choice a b

MkLeft : a -> FunkyEither a b
MkLeft x = MkFunkyEither True x

MkRight : b -> FunkyEither a b
MkRight y = MkFunkyEither False y

record FuncDef where 
Afhængig record FuncDef Skal kende fEnv, og have argType som input og RetType output 
Body skal bruge Variable
  constructor MkFuncDef
  body: Exp return_type

--f(x) = x+2
--MkFuncDef (Just "f") "x" Tint Tint (ExpPlus (ExpVar "x") (ExpVal 2))


data FullProgram : 

FuncEnv: Type --afhænge af fEnv
FuncEnv = List FuncDef

-- data FuncDef : Vect n TyExp -> TyExp -> TyExp -> Type where
-- funcDef : (func_name: String) -> (arg_name: String) -> (arg_type: TyExp) -> (func_body: Exp cntxt t) -> FuncDef cntxt t t

-}
