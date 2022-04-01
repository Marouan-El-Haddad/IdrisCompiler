module Main
import Data.SnocList

|||Abstract Syntax Tree for Integer with addition, subtraction and multiplication
data ASTExpr 
    = EIntLit Int 
    | EAddition ASTExpr ASTExpr 
    | ESubtraction ASTExpr ASTExpr 
    | EMultiplication ASTExpr ASTExpr

|||Evaluate Abstract Syntax Tree and return value
evaluate : ASTExpr -> Int
evaluate (EIntLit a) = a
evaluate (EAddition a b) = evaluate a + evaluate b
evaluate (ESubtraction a b) = evaluate a - evaluate b
evaluate (EMultiplication a b) = evaluate a * evaluate b

|||Instruction syntax
data Instruction = Push Int | Add | Subtract | Mult

|||Compile expression to a list of instruction
compile : ASTExpr -> List Instruction 
compile (EIntLit a) =  [Push a]
compile (EAddition a b) = compile a ++ compile b ++ [Add] 
compile (ESubtraction a b) = compile a ++ compile b ++ [Subtract] 
compile (EMultiplication a b) = compile a ++ compile b ++ [Mult]

|||Writing the instructions to a file for the stack machine to execute
print : Instruction -> String
print (Push a) = "Push " ++ show a
print Add = "Add"
print Subtract = "Subtract"
print Mult = "Mult"

|||Writing the List instructions to a file for the stack machine to execute (tail recursive and linear time by using stringMap)
stringMap : (a -> String) -> List a -> String
stringMap f = go Lin
  where go : SnocList String -> List a -> String
        go sx []         = concat (sx <>> Nil)
        go sx (x :: Nil) = go (sx :< f x) Nil
        go sx (x :: xs)  = go (sx :< f x :< "\n") xs

printList : List Instruction -> String
printList = stringMap print

--Taking a machine configuration to the next one by executing a single step of computations
runInstruction : List Int -> Instruction -> Maybe (List Int)
runInstruction xs (Push a) = Just (a :: xs)
runInstruction (x :: y :: xs) Add = Just ((x + y) :: xs)
runInstruction (x :: y :: xs) Subtract = Just ((y - x) :: xs) 
runInstruction (x :: y :: xs) Mult = Just ((x * y) :: xs)
runInstruction _ _ = Nothing

|||Taking a machine configuration to the next one by executing multiple step of computations
runInstructions: List Instruction -> List Int -> Maybe (List Int)
runInstructions xs ys = foldlM runInstruction ys xs

runAll : runInstructions (compile (e : ASTExpr)) [] -> Maybe (List Int)

runAll2 : (e : ASTExpr) -> evaluate -> Maybe (List Int)
-- implementation

test_runInstruction_add : runInstruction [1, 2] Add = Just [3]
test_runInstruction_add = Refl

test_runInstruction_sub : runInstruction [2, 1] Subtract = Just [-1]
test_runInstruction_sub = Refl


test_runInstructions_add : runInstructions [Push 1, Push 2, Add] [] = Just [3]
test_runInstructions_add = Refl

test_runInstructions_sub : runInstructions [Push 1, Push 2, Subtract] [] = Just [-1]
test_runInstructions_sub = Refl

test3_runAll : runInstructions (compile (EAddition (EIntLit 2) (EIntLit 3))) [] === Just [evaluate (EAddition (EIntLit 2) (EIntLit 3))]
test3_runAll = Refl

main : IO ()
main = ?hole
