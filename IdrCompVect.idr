module Main
import Data.Vect

data Expr
    = EIntLit Int
    | EAddition Expr Expr
    | ESubtraction Expr Expr
    | EMultiplication Expr Expr

|||Using the Num interface to define basic numerical arithmetic
Num (Expr) where
    (+) = EAddition
    (*) = EMultiplication
    fromInteger = EIntLit . fromInteger

|||Using the Neg interface to define operations on numbers which can be negative.
Neg (Expr) where
    negate x = 0 - x
    (-) = ESubtraction

total
StackType : Type
StackType = Nat

total
Stack : StackType -> Type
Stack n = Vect n Int

data Code : StackType -> StackType -> Type where
    Combine : Code a b -> Code b c -> Code a c
    Push : Int -> Code n (S n)
    Add : Code (S (S n)) (S n)
    Sub : Code (S (S n)) (S n)
    Mult : Code (S (S n)) (S n)
    Pop : Code (S n) n

total
compile : Expr -> Code k (S k)
compile (EIntLit x) = Push x
compile (EAddition x y) = Combine (compile x) (Combine (compile y) Add)
compile (ESubtraction x y) = Combine (compile x) (Combine (compile y) Sub)
compile (EMultiplication x y) = Combine (compile x) (Combine (compile y) Mult)

total
exec : Code n m -> Stack n -> Stack m
exec (Combine x y) xs = exec y (exec x xs)
exec (Push x) xs = x::xs
exec Add (x0::x1::xs) = (x0 + x1) :: xs
exec Sub (x0::x1::xs) = (x1 - x0) :: xs
exec Mult (x0::x1::xs) = (x0 * x1) :: xs
exec Pop (x :: xs) = xs

total
eval : Expr -> Int
eval (EIntLit a) = a
eval (EAddition a b) = eval a + eval b
eval (ESubtraction a b) = eval a - eval b
eval (EMultiplication a b) = eval a * eval b

total
top : Stack (S n) -> Int
top (x :: xs) = x

total
runAll: (e : Expr) -> Int
runAll e = top(exec(compile(e)) [])

total
runAll2: (e : Expr) -> Int
runAll2 e = eval(e)

main : IO ()
main = ?hole2

-- Tests

test_both_RunAlls_add2 : exec Add (exec (compile 2) (eval 3 :: s)) = (eval 2 + eval 3) :: s
test_both_RunAlls_add2 = Refl

test_both_RunAlls_add : runAll (2+3) = runAll2 (2+3)
test_both_RunAlls_add = Refl

test_both_RunAlls_sub : runAll (2-3) = runAll2 (2-3)
test_both_RunAlls_sub = Refl

test_both_RunAlls_mul : runAll (10*2) = runAll2 (10*2)
test_both_RunAlls_mul = Refl

total
addComm : (a : Nat) -> (b : Nat) -> a + b = b + a
addComm 0 b = sym(plusZeroRightNeutral b)
addComm (S k) b = rewrite addComm k b in
                    plusSuccRightSucc b k

0
addCommutative : (x, y : Int) -> x + y = y + x

0
multCommutative : (x, y : Int) -> x * y = y * x

0
subCommutative : (x, y : Int) -> x - y = y - x

correct : (e : Expr) -> (s : Stack n) -> exec (compile e) s = eval e :: s
correct (EIntLit x) s = Refl
correct (EAddition x y) s = rewrite correct x s in 
                            rewrite correct y (eval x :: s) in
                            rewrite addCommutative (eval y) (eval x) in
                            Refl
correct (ESubtraction x y) s = rewrite correct x s in 
                            rewrite correct y (eval x :: s) in
                            Refl
correct (EMultiplication x y) s = rewrite correct x s in 
                            rewrite correct y (eval x :: s) in
                            rewrite multCommutative (eval y) (eval x) in
                            Refl
