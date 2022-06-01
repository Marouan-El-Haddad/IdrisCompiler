module Main
import Data.Vect

-- Ultimately I want to be able to mix booleans and ints anywhere in the expression. 
-- For that I need to index Expr by the type of the value it evaluates to ie
data Expr2 : Type -> Type where
EIntLit2 : Expr2 Int
EAddition2 : Expr2 Int -> Expr2 Int -> Expr2 Int
EIfThenElse2 : (cond : Expr2 Bool) -> (true : Expr2 a) -> (false : Expr2 a) -> Expr2 a
EIfEq2 : (x : Expr2 Int) -> (y : Expr2 Int) -> Expr2 Bool

data Expr
    = EIntLit Int
    | EAddition Expr Expr
    | ESubtraction Expr Expr
    | EMultiplication Expr Expr
    | EIfEq Expr Expr Expr Expr
--    | EIfThenElse Expr Expr Expr Expr

total
StackDepth : Type
StackDepth = Nat

total
Stack : StackDepth -> Type
Stack n = Vect n Int

data Code : StackDepth -> StackDepth -> Type where
    Combine : Code a b -> Code b c -> Code a c
    Push : Int -> Code n (S n)
    Add : Code (S (S n)) (S n)
    Sub : Code (S (S n)) (S n)
    Mult : Code (S (S n)) (S n)
    Pop : Code (S n) n
    IfEq : (true : Code n m) -> (false : Code n m) -> Code (S (S n)) m
--    IfThenElse : (true : Code n m) -> (false : Code n m) -> Code (S n) m

total
compile : Expr -> Code k (S k)
compile (EIntLit x) = Push x
compile (EAddition x y) = Combine (compile x) (Combine (compile y) Add)
compile (ESubtraction x y) = Combine (compile x) (Combine (compile y) Sub)
compile (EMultiplication x y) = Combine (compile x) (Combine (compile y) Mult)
compile (EIfEq x y a b) = Combine (compile x) (Combine (compile y) (IfEq (compile a) (compile b)))
--compile (EIfThenElse x y a b) = ?compile_missing_case_1

total
exec : Code n m -> Stack n -> Stack m
exec (Combine x y) xs = exec y (exec x xs)
exec (Push x) xs = x::xs
exec Add (x0::x1::xs) = (x1 + x0) :: xs
exec Sub (x0::x1::xs) = (x1 - x0) :: xs
exec Mult (x0::x1::xs) = (x1 * x0) :: xs
exec Pop (x :: xs) = xs
exec (IfEq a b) (x :: y :: xs) = (if x == y then exec a xs else exec b xs)
--exec (IfThenElse _ _) _ = ?exec_missing_case_1

total
eval : Expr -> Int
eval (EIntLit a) = a
eval (EAddition a b) = eval a + eval b
eval (ESubtraction a b) = eval a - eval b
eval (EMultiplication a b) = eval a * eval b
eval (EIfEq x y a b) = (if eval x == eval y then eval a else eval b)

total
top : Stack (S n) -> Int
top (x :: xs) = x

total
runAll: (e : Expr) -> Int
runAll e = top(exec(compile(e)) [])

total
runAll2: (e : Expr) -> Int
runAll2 e = eval(e)
