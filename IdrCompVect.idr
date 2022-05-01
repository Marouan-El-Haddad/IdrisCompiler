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

StackType : Type
StackType = Nat

Stack : StackType -> Type
Stack n = Vect n Int

data Code : StackType -> StackType -> Type where
    Combine : Code a b -> Code b c -> Code a c -- combine two Code into one
    Push : Int -> Code n (S n)
    Add : Code (S (S n)) (S n)
    Sub : Code (S (S n)) (S n)
    Mult : Code (S (S n)) (S n)
    Pop : Code (S n) n

compile : Expr -> Code k (S k)
compile (EIntLit x) = Push x
compile (EAddition x y) = Combine (compile y) (Combine (compile y) Add)
compile (ESubtraction x y) = Combine (compile y) (Combine (compile y) Sub)
compile (EMultiplication x y) = Combine (compile y) (Combine (compile y) Mult)

top : Stack (S n) -> Int
top (x :: xs) = x

exec : Code n m -> Stack n -> Stack m
exec (Combine x y) xs = exec y(exec x(xs))
exec (Push x) xs = x::xs
exec Add (x0::x1::xs) = (x0 + x1) :: xs
exec Sub (x0::x1::xs) = (x0 - x1) :: xs
exec Mult (x0::x1::xs) = (x0 * x1) :: xs
exec Pop (x :: xs) = xs

main : IO ()
main = ?hole2
