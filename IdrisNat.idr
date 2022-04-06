module Main
import Data.SnocList

|||Abstract Syntax Tree for Nateger with addition, subtraction and multiplication
data ASTExpr
    = ENatLit Nat
    | EAddition ASTExpr ASTExpr
    | EMultiplication ASTExpr ASTExpr

|||Instruction syntax
data Instruction = Push Nat | Add | Mult

|||Compile expression to a list of instruction
total
compile : ASTExpr -> List Instruction
compile (ENatLit a) =  [Push a]
compile (EAddition a b) = compile a ++ compile b ++ [Add]
compile (EMultiplication a b) = compile a ++ compile b ++ [Mult]

|||Writing the instructions to a file for the stack machine to execute
total
prNat : Instruction -> String
prNat (Push a) = "Push " ++ show a
prNat Add = "Add"
prNat Mult = "Mult"

|||Helper function for prNatList (tail recursive and linear time by using stringMap)
total
stringMap : (a -> String) -> List a -> String
stringMap f = go Lin
  where go : SnocList String -> List a -> String
        go sx []         = concat (sx <>> Nil)
        go sx (x :: Nil) = go (sx :< f x) Nil
        go sx (x :: xs)  = go (sx :< f x :< "\n") xs

|||Writing the List instructions to a file for the stack machine to execute
total
prNatList : List Instruction -> String
prNatList = stringMap prNat

--Taking a machine configuration to the next one by executing a single step of computations
total
runInstruction : List Nat -> Instruction -> Maybe (List Nat)
runInstruction xs (Push a) = Just (a :: xs)
runInstruction (x :: y :: xs) Add = Just ((x + y) :: xs)
runInstruction (x :: y :: xs) Mult = Just ((x * y) :: xs)
runInstruction _ _ = Nothing

|||Taking a machine configuration to the next one by executing multiple step of computations
total
runInstructions: List Instruction -> List Nat -> Maybe (List Nat)
runInstructions xs ys = foldlM runInstruction ys xs

|||Evaluate Abstract Syntax Tree and return value
total
evaluate : ASTExpr -> Nat
evaluate (ENatLit a) = a
evaluate (EAddition a b) = evaluate a + evaluate b
evaluate (EMultiplication a b) = evaluate a * evaluate b

|||Universal statement linking the evaluation path via compile followed by RunInstructions
total
runAll: (e : ASTExpr) -> Maybe (List Nat)
runAll e = runInstructions(compile(e)) []

|||Universal statement linking the evaluation path via evaluate
total
runAll2: (e : ASTExpr) -> Maybe (List Nat)
runAll2 e = Just([evaluate(e)])

-- plusZeroRightNeutralNat : (x : Nat) -> x + 0 = 0
--theorem
addReduces : (n: Nat) -> runAll (EAddition (ENatLit n) (ENatLit 0)) = Just [n]
--proof
addReduces n = Refl

main : IO ()
main = ?hole
