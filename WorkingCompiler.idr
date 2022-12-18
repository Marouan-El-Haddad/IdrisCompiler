--import Data.Vect: 
--This imports the Vect module from the Data package, which provides functions for working with vector data structures.
import Data.Vect
--%default total: 
--This directive specifies that the total attribute should be applied to all definitions in the current module by default. 
--This attribute indicates that a function is total, meaning that it is guaranteed to return a value for all possible inputs.
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


--I then use the data type TyExp, to define a function Val.
--First line is a function type with TyExp as the input and a Type as output. 
--The next lines are the definition of the function. 
--A Val with Tint as argument will evaluate to an Int, and a Val with Tbool will evaluate to a Bool.
--The function Val is a type family, which means that it is a function that maps a type expression to a corresponding type.
--data TyExp: 
--This defines a new data type called TyExp, which represents the types of expressions in the language. 
--It has two constructors: Tint for the type of integers and Tbool for the type of booleans.
data TyExp
    = Tint
    | Tbool

--Val : TyExp -> Type: 
--This defines a type family called Val, which maps a type expression to a corresponding type. 
--For example, Val Tint is the type Int and Val Tbool is the type Bool.
Val : TyExp -> Type
Val Tint = Int
Val Tbool = Bool


{- 
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

HasTypeVar : (i : Fin n) -> Vect n TyExp -> TyExp -> Type: 
This defines a type family called HasTypeVar, 
which takes a natural number i (represented as a value of the type Fin n), a vector of type expressions Vect n TyExp, and a type expression TyExp, and returns a type. 
This type family is used to represent variables in the language, with i representing the index of the variable in the vector of type expressions.

StopVar : HasTypeVar FZ (tVar :: vcntxt) tVar: This defines a constructor for the HasTypeVar type family, called StopVar. 
It takes a value FZ of the type Fin 0, a vector of type expressions (tVar :: vcntxt), and a type expression tVar, and returns a value of the HasTypeVar type. 
FZ is a special value of the type Fin 0 representing the zero element of a finite type with zero elements.

PopVar : HasTypeVar kFin vcntxt tVar -> HasTypeVar (FS kFin) (uVar :: vcntxt) tVar: 
This defines another constructor for the HasTypeVar type family, called PopVar. 
It takes a value of the type HasTypeVar kFin vcntxt tVar and returns a value of the type HasTypeVar (FS kFin) (uVar :: vcntxt) tVar. 
FS kFin is a value of the type Fin (S k), where S k is the successor of k. This constructor is used to move to the next element in the vector of type expressions.
-}
data HasTypeVar : (i : Fin n) -> Vect n TyExp -> TyExp -> Type where
    StopVar : HasTypeVar FZ (tVar :: vcntxt) tVar 
    PopVar  : HasTypeVar kFin vcntxt tVar 
           -> HasTypeVar (FS kFin) (uVar :: vcntxt) tVar

{-
data Exp : (vEnv: Vect n TyExp) -> (TyExp, TyExp) -> TyExp -> Type: 
This defines a new data type called Exp, which represents expressions in the language. 
It takes three arguments: a vector of type expressions Vect n TyExp representing the type environment, 
a pair of type expressions (TyExp, TyExp) representing the function environment, and a type expression TyExp representing the type of the expression.

ExpVar : HasTypeVar iFin vEnv t -> Exp vEnv fEnv t: This defines a constructor for the Exp type called ExpVar, which takes a value of the type HasTypeVar iFin vEnv t and returns a value of the type Exp vEnv fEnv t. This constructor represents a variable expression in the language, with the value of HasTypeVar iFin vEnv t representing the type and location of the variable.

ExpVal : (x : Int) -> Exp vEnv fEnv Tint: This defines a constructor for the Exp type called ExpVal, which takes an integer x and returns a value of the type Exp vEnv fEnv Tint. This constructor represents a literal integer value in the language.

ExpAddition : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint: This defines a constructor for the Exp type called ExpAddition, which takes two values of the type Exp vEnv fEnv Tint and returns a value of the same type. This constructor represents an addition expression in the language, with the two arguments representing the operands.

ExpSubtraction : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint: This defines a constructor for the Exp type called ExpSubtraction, which takes two values of the type Exp vEnv fEnv Tint and returns a value of the same type. This constructor represents a subtraction expression in the language, with the two arguments representing the operands.

ExpMultiplication : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint: This defines a constructor for the Exp type called ExpMultiplication, which takes two values of the type Exp vEnv fEnv Tint and returns a value of the same type. This constructor represents a multiplication expression in the language, with the two arguments representing the operands.

ExpIfThenElse : Exp vEnv fEnv Tbool -> Exp vEnv fEnv t -> Exp vEnv fEnv t -> Exp vEnv fEnv t: This defines a constructor for the Exp type called ExpIfThenElse, which takes three values of the type Exp vEnv fEnv t. The first argument has type Exp vEnv fEnv Tbool, representing the condition of the if expression, and the second and third arguments have the same type Exp vEnv fEnv t, representing the then and else branches of the expression, respectively. This constructor represents an if expression in the language.

ExpOr : Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool: This defines a constructor for the Exp type called ExpOr, which takes two values of the type Exp vEnv fEnv Tbool and returns a value of the same type. This constructor represents an or expression in the language, with the two arguments representing the operands.

ExpAnd : Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool: This defines a constructor for the Exp type called ExpAnd, which takes two values of the type Exp vEnv fEnv Tbool and returns a value of the same type. This constructor represents an and expression in the language, with the two arguments representing the operands.

ExpNot : Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool: This defines a constructor for the Exp type called ExpNot, which takes a value of the type Exp vEnv fEnv Tbool and returns a value of the same type. This constructor represents a not expression in the language, with the argument representing the operand.

ExpEqual : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool: This defines a constructor for the Exp type called ExpEqual, which takes two values of the type Exp vEnv fEnv Tint and returns a value of the type Exp vEnv fEnv Tbool. This constructor represents an equality expression in the language, with the two arguments representing the operands.

ExpNotEqual : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool: This defines a constructor for the Exp type called ExpNotEqual, which takes two values of the type Exp vEnv fEnv Tint and returns a value of the type Exp vEnv fEnv Tbool. This constructor represents a non-equality expression in the language, with the two arguments representing the operands.

ExpLessThan : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool: This defines a constructor for the Exp type called ExpLessThan, which takes two values of the type Exp vEnv fEnv Tint and returns a value of the type Exp vEnv fEnv Tbool. This constructor represents a less-than expression in the language, with the two arguments representing the operands.

ExpLessThanEqual : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool: This defines a constructor for the Exp type called ExpLessThanEqual, which takes two values of the type Exp vEnv fEnv Tint and returns a value of the type Exp vEnv fEnv Tbool. This constructor represents a less-than-or-equal expression in the language, with the two arguments representing the operands.

ExpGreaterThan : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool: This defines a constructor for the Exp type called ExpGreaterThan, which takes two values of the type Exp vEnv fEnv Tint and returns a value of the type Exp vEnv fEnv Tbool. This constructor represents a greater-than expression in the language, with the two arguments representing the operands.

ExpGreaterThanEqual : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool: This defines a constructor for the Exp type called ExpGreaterThanEqual, which takes two values of the type Exp vEnv fEnv Tint and returns a value of the type Exp vEnv fEnv Tbool. This constructor represents a greater-than-or-equal expression in the language, with the two arguments representing the operands.

ExpFuncCall: Exp vEnv (s,t) s -> Exp vEnv (s,t) t: This defines a constructor for the Exp type called ExpFuncCall, which takes a value of the type Exp vEnv (s,t) s and returns a value of the type Exp vEnv (s,t) t. This constructor represents a function call expression in the language, with the argument representing the function to be called and the return type representing the return type of the function.
-}
data Exp : (vEnv: Vect n TyExp) -> (TyExp, TyExp) -> TyExp -> Type where
  ExpVar : HasTypeVar iFin vEnv t -> Exp vEnv fEnv t
  ExpVal : (x : Int) -> Exp vEnv fEnv Tint
  ExpAddition : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpSubtraction : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpMultiplication : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpIfThenElse : Exp vEnv fEnv Tbool -> Exp vEnv fEnv t -> Exp vEnv fEnv t -> Exp vEnv fEnv t
  ExpOr : Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool
  ExpAnd : Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool
  ExpNot : Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool
  ExpEqual : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpNotEqual : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpLessThan : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpLessThanEqual : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpGreaterThan : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpGreaterThanEqual : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpFuncCall: Exp vEnv (s,t) s -> Exp vEnv (s,t) t


{- 
record FunDecl where: This declares a record type called FunDecl with the following fields:

fd_var_type: TyExp: This field represents the type of the variable being passed to the function.
fd_return_type: TyExp: This field represents the return type of the function.
body: Exp [fd_var_type] (fd_var_type, fd_return_type) fd_return_type: This field represents the body of the function, which is an expression of type Exp [fd_var_type] (fd_var_type, fd_return_type) fd_return_type.
-}
record FunDecl where
  constructor MkFunDecl
  fd_var_type: TyExp
  fd_return_type: TyExp
  body: Exp [fd_var_type] (fd_var_type, fd_return_type) fd_return_type

{-
record OpenProgram where: This declares a record type called OpenProgram with the following fields:

op_funDecl : FunDecl: This field represents the function declaration of the program.
op_return_type: TyExp: This field represents the return type of the program.
op_arg_type : TyExp: This field represents the type of the argument being passed to the program.
val_arg : Val op_arg_type: This field represents the argument being passed to the program.
op_mainExp : Exp [op_arg_type] (op_funDecl.fd_var_type, op_funDecl.fd_return_type) op_return_type: This field represents the main expression of the program, which is an expression of type Exp [op_arg_type] (op_funDecl.fd_var_type, op_funDecl.fd_return_type) op_return_type.
-}
record OpenProgram where
  constructor MkOpenProgram
  op_funDecl : FunDecl
  op_return_type: TyExp
  op_arg_type : TyExp
  val_arg : Val op_arg_type
  op_mainExp : Exp [op_arg_type] (op_funDecl.fd_var_type, op_funDecl.fd_return_type) op_return_type


{- 
record Program where: This declares a record type called Program with the following fields:

p_funDecl: FunDecl: This field represents the function declaration of the program.
p_return_type: TyExp: This field represents the return type of the program.
p_mainExp: Exp [] (p_funDecl.fd_var_type, p_funDecl.fd_return_type) p_return_type: This field represents the main expression of the program, which is an expression of type Exp [] (p_funDecl.fd_var_type, p_funDecl.fd_return_type) p_return_type.
-}
record Program where
  constructor MkProgram
  p_funDecl: FunDecl
  p_return_type: TyExp
  p_mainExp: Exp [] (p_funDecl.fd_var_type, p_funDecl.fd_return_type) p_return_type


{-
data VarEnv : Vect n TyExp -> Type where: This declares a data type called VarEnv that takes a value of the type Vect n TyExp and represents a variable environment. The VarEnv type has the following constructors:

Nil : VarEnv Nil: This constructor represents an empty variable environment.
(::) : Val a -> VarEnv ecntxt -> VarEnv (a :: ecntxt): This constructor represents a non-empty variable environment, with the Val a value representing a variable and the VarEnv ecntxt value representing the rest of the environment.
-}
data VarEnv : Vect n TyExp -> Type where
    Nil  : VarEnv Nil
    (::) : Val a 
            -> VarEnv ecntxt 
            -> VarEnv (a :: ecntxt)

{-
lookupVar : HasTypeVar i lcontex t -> VarEnv lcontex -> Val t: This is a function that takes a value of the type HasTypeVar i lcontex t and a value of the type VarEnv lcontex, and returns a value of the type Val t. The function looks up the value of the variable in the given environment using the HasTypeVar value.
-}
lookupVar : HasTypeVar i lcontex t -> VarEnv lcontex -> Val t
lookupVar StopVar (x :: xs) = x
lookupVar (PopVar k) (x :: xs) = lookupVar k xs


{-
evalOpenProgram : OpenProgram -> Val op_return_type: This is a function that takes a value of the type OpenProgram, and returns a value of the type Val op_return_type. The function evaluates the main expression of the open program using the given argument.
-}
evalOpenProg : (op: OpenProgram) -> Val op.op_return_type
evalOpenProg (MkOpenProgram op_funDecl op_return_type op_arg_type val_arg (ExpVar x)) = lookupVar x (val_arg :: Nil)
evalOpenProg (MkOpenProgram op_funDecl Tint op_arg_type val_arg (ExpVal x)) = x
evalOpenProg (MkOpenProgram op_funDecl Tint op_arg_type val_arg (ExpAddition x y)) = evalOpenProg (assert_smaller x $ MkOpenProgram op_funDecl Tint op_arg_type val_arg x) + evalOpenProg (assert_smaller y $ MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tint op_arg_type val_arg (ExpSubtraction x y)) = evalOpenProg (assert_smaller x $ MkOpenProgram op_funDecl Tint op_arg_type val_arg x) - evalOpenProg (assert_smaller y $ MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tint op_arg_type val_arg (ExpMultiplication x y)) = evalOpenProg (assert_smaller x $ MkOpenProgram op_funDecl Tint op_arg_type val_arg x) * evalOpenProg (assert_smaller y $ MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl op_return_type op_arg_type val_arg (ExpIfThenElse x y z)) = if evalOpenProg (assert_smaller x $ MkOpenProgram op_funDecl Tbool op_arg_type val_arg x) then evalOpenProg (assert_smaller y $ MkOpenProgram op_funDecl op_return_type op_arg_type val_arg y) else evalOpenProg (assert_smaller z $ MkOpenProgram op_funDecl op_return_type op_arg_type val_arg z)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpOr x y)) = evalOpenProg (assert_smaller x $ MkOpenProgram op_funDecl Tbool op_arg_type val_arg x) || evalOpenProg (assert_smaller y $ MkOpenProgram op_funDecl Tbool op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpAnd x y)) = evalOpenProg (assert_smaller x $ MkOpenProgram op_funDecl Tbool op_arg_type val_arg x) && evalOpenProg (assert_smaller y $ MkOpenProgram op_funDecl Tbool op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpNot x)) = not $ evalOpenProg (assert_smaller x $ MkOpenProgram op_funDecl Tbool op_arg_type val_arg x)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpEqual x y)) = evalOpenProg (assert_smaller x $ MkOpenProgram op_funDecl Tint op_arg_type val_arg x) == evalOpenProg (assert_smaller y $ MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpNotEqual x y)) = evalOpenProg (assert_smaller x $ MkOpenProgram op_funDecl Tint op_arg_type val_arg x) /= evalOpenProg (assert_smaller y $ MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpLessThan x y)) = evalOpenProg (assert_smaller x $ MkOpenProgram op_funDecl Tint op_arg_type val_arg x) < evalOpenProg (assert_smaller y $ MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpLessThanEqual x y)) = evalOpenProg (assert_smaller x $ MkOpenProgram op_funDecl Tint op_arg_type val_arg x) <= evalOpenProg (assert_smaller y $ MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpGreaterThan x y)) = evalOpenProg (assert_smaller x $ MkOpenProgram op_funDecl Tint op_arg_type val_arg x) > evalOpenProg (assert_smaller y $ MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpGreaterThanEqual x y)) = evalOpenProg (assert_smaller x $ MkOpenProgram op_funDecl Tint op_arg_type val_arg x) >= evalOpenProg (assert_smaller y $ MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl (op_funDecl.fd_return_type) op_arg_type val_arg (ExpFuncCall x)) 
                = evalOpenProg (
                    MkOpenProgram op_funDecl (op_funDecl.fd_return_type) op_arg_type val_arg (
                      ExpFuncCall x
                    ) 
                  ) 

{-
evalProgram : Program -> Val p_return_type: This is a function that takes a value of the type Program, and returns a value of the type Val p_return_type. The function evaluates the main expression of the program.
-}
evalProg : (p: Program) -> Val p.p_return_type
evalProg (MkProgram _ _ (ExpVar StopVar)) impossible
evalProg (MkProgram _ _ (ExpVar (PopVar x))) impossible
evalProg (MkProgram p_funDecl Tint (ExpVal x)) = x
evalProg (MkProgram p_funDecl Tint (ExpAddition x y)) = evalProg (assert_smaller x $ MkProgram p_funDecl Tint x) + evalProg (assert_smaller y $ MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tint (ExpSubtraction x y)) = evalProg (assert_smaller x $ MkProgram p_funDecl Tint x) - evalProg (assert_smaller y $ MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tint (ExpMultiplication x y)) = evalProg (assert_smaller x $ MkProgram p_funDecl Tint x) * evalProg (assert_smaller y $ MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl p_return_type (ExpIfThenElse x y z)) = if evalProg (assert_smaller x $ MkProgram p_funDecl Tbool x) then evalProg (assert_smaller y $ MkProgram p_funDecl p_return_type y) else evalProg (assert_smaller z $ MkProgram p_funDecl p_return_type z)
evalProg (MkProgram p_funDecl Tbool (ExpOr x y)) = evalProg (assert_smaller x $ MkProgram p_funDecl Tbool x) || evalProg (assert_smaller y $ MkProgram p_funDecl Tbool y)
evalProg (MkProgram p_funDecl Tbool (ExpAnd x y)) = evalProg (assert_smaller x $ MkProgram p_funDecl Tbool x) && evalProg (assert_smaller y $ MkProgram p_funDecl Tbool y)
evalProg (MkProgram p_funDecl Tbool (ExpNot x)) = not $ evalProg (assert_smaller x $ MkProgram p_funDecl Tbool x)
evalProg (MkProgram p_funDecl Tbool (ExpEqual x y)) = evalProg (assert_smaller x $ MkProgram p_funDecl Tint x) == evalProg (assert_smaller y $ MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tbool (ExpNotEqual x y)) = evalProg (assert_smaller x $ MkProgram p_funDecl Tint x) /= evalProg (assert_smaller y $ MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tbool (ExpLessThan x y)) = evalProg (assert_smaller x $ MkProgram p_funDecl Tint x) < evalProg (assert_smaller y $ MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tbool (ExpLessThanEqual x y)) = evalProg (assert_smaller x $ MkProgram p_funDecl Tint x) <= evalProg (assert_smaller y $ MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tbool (ExpGreaterThan x y)) = evalProg (assert_smaller x $ MkProgram p_funDecl Tint x) > evalProg (assert_smaller y $ MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tbool (ExpGreaterThanEqual x y)) = evalProg (assert_smaller x $ MkProgram p_funDecl Tint x) >= evalProg (assert_smaller y $ MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl (p_funDecl.fd_return_type) (ExpFuncCall x)) 
                = evalOpenProg (
                    MkOpenProgram p_funDecl (p_funDecl.fd_return_type) p_funDecl.fd_var_type (
                      evalProg (assert_smaller x $
                        MkProgram p_funDecl (p_funDecl.fd_var_type) x
                        )
                    ) p_funDecl.body 
                  )

