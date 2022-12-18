import Data.Vect
%default total 

data TyExp
    = Tint
    | Tbool

Val : TyExp -> Type
Val Tint = Int
Val Tbool = Bool

data HasTypeVar : (i : Fin n) -> Vect n TyExp -> TyExp -> Type where
    StopVar : HasTypeVar FZ (tVar :: vcntxt) tVar 
    PopVar  : HasTypeVar kFin vcntxt tVar 
           -> HasTypeVar (FS kFin) (uVar :: vcntxt) tVar

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
  

record FunDecl where
  constructor MkFunDecl
  fd_var_type: TyExp
  fd_return_type: TyExp
  body: Exp [fd_var_type] (fd_var_type, fd_return_type) fd_return_type

record OpenProgram where
  constructor MkOpenProgram
  op_funDecl : FunDecl
  op_return_type: TyExp
  op_arg_type : TyExp
  val_arg : Val op_arg_type
  op_mainExp : Exp [op_arg_type] (op_funDecl.fd_var_type, op_funDecl.fd_return_type) op_return_type

record Program where
  constructor MkProgram
  p_funDecl: FunDecl
  p_return_type: TyExp
  p_mainExp: Exp [] (p_funDecl.fd_var_type, p_funDecl.fd_return_type) p_return_type

data VarEnv : Vect n TyExp -> Type where
    Nil  : VarEnv Nil
    (::) : Val a 
            -> VarEnv ecntxt 
            -> VarEnv (a :: ecntxt)

lookupVar : HasTypeVar i lcontex t -> VarEnv lcontex -> Val t
lookupVar StopVar (x :: xs) = x
lookupVar (PopVar k) (x :: xs) = lookupVar k xs


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



-- Define a function that adds two integers
add : FunDecl
add = MkFunDecl Tint Tint (ExpAddition (ExpVal 1) (ExpVal 2))

-- Create an OpenProgram value that includes the add function and the necessary return type
prog1 : OpenProgram
prog1 = MkOpenProgram add Tint Tint 3 (ExpFuncCall (ExpVar (StopVar)))


-- Define a function that returns the square of an integer
square : FunDecl
square = MkFunDecl Tint Tint (ExpMultiplication (ExpVar (StopVar)) (ExpVar (StopVar)))

-- Create an OpenProgram value that includes the square function and the necessary return type
prog2 : OpenProgram
prog2 = MkOpenProgram square Tint Tint 3 (ExpMultiplication (ExpVal 2) (ExpVal 2))


-- Define a function that returns the square of an integer if the input is greater than 2, and the input itself otherwise
squareOrInput : FunDecl
squareOrInput = MkFunDecl Tint Tint (ExpIfThenElse (ExpGreaterThan (ExpVar (StopVar)) (ExpVal 2)) (ExpMultiplication (ExpVar (StopVar)) (ExpVar (StopVar))) (ExpVar (StopVar)))

-- Create an OpenProgram value that includes the squareOrInput function and the necessary return type
prog3 : OpenProgram
prog3 = MkOpenProgram squareOrInput Tint Tint 3 (ExpIfThenElse (ExpGreaterThan (ExpVal 2) (ExpVal 1)) (ExpMultiplication (ExpVal 2) (ExpVal 2)) (ExpVal 1))

-- Define a function that returns True if the input is greater than 10, and False otherwise
isGreaterThanTen : FunDecl
isGreaterThanTen = MkFunDecl Tint Tbool (ExpGreaterThan (ExpVar (StopVar)) (ExpVal 10))

-- Create an OpenProgram value that includes the isGreaterThanTen function and the necessary return type
prog4 : OpenProgram
prog4 = MkOpenProgram isGreaterThanTen Tbool Tint 12 (ExpGreaterThan (ExpVal 12) (ExpVal 10))

--evalOpenProg prog
--evalOpenProg prog2
--evalOpenProg prog3
--evalOpenProg prog4
--evalOpenProg prog5
