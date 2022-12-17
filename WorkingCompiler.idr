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
evalProg (MkProgram p_funDecl (p_funDecl.fd_return_type) (ExpFuncCall x)) 
                = evalOpenProg (
                    MkOpenProgram p_funDecl (p_funDecl.fd_return_type) p_funDecl.fd_var_type (
                      evalProg (assert_smaller x $
                        MkProgram p_funDecl (p_funDecl.fd_var_type) x
                        )
                    ) p_funDecl.body 
                  )
