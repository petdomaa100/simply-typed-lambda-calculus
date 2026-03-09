import Distribution.Simple.Utils (safeHead)
import Text.Printf (printf)

-- =====
-- Simply-Typed Lambda Calculus (STLC)
-- =====

-- In all programming languages, the source code gets parsed into an
-- Abstract Syntax Tree (AST) that represents the program. Nodes of
-- this tree are called Terms. In STLC, there are 4 kinds of terms:
--
-- 1) Unit values. The term `Unit` represents a constant value of type `TUnit`.
-- It's sometimes also called a "literal".
--
-- 2) Function definitions. The term `Lam inType body` defines a function
-- that takes an input of type `inType` and returns whatever `body` computes.
-- In mathematical language, a function definition is called "Lambda abstraction",
-- and its input variable is called a "binder". Example: `Lam someType (Var 0)`
-- is the identity function `λx.x`.
--
-- 3) Variable references. The term `Var n` refers to a variable "called" `n` in
-- a body of a function definition. The "name" of a variable is represented as
-- an integer. `Var 0` refers to the input variable of the current function, `Var 1`
-- refers to the input variable of the function 1 level up, etc. `n` is called the
-- Bruijn index.
--
-- 4) Function Calls. The term `Ap fn arg` calls function `fn` with the argument
-- `arg`. In mathematical language, "calling" a function is referred to as function
-- application.
data Term
  = Unit
  | Lam Type Term
  | Var Int
  | Ap Term Term
  deriving (Eq)

-- A type of a term defines the kind of value it evaluates to. In STLC, only unit values
-- and function definitions have types. Variable references and function applications get
-- their types inferred. There are only 2 kinds of types in STLC:
--
-- 1) Unit type. The type `TUnit` represents the type of constant, "hard-coded" values.
--
-- 2) Function types. The type `TFunc inType outType` represents functions that take
-- an input of type `inType` and return a value of type `outType`.
data Type
  = TUnit
  | TFunc Type Type
  deriving (Eq)

-- The value context is a stack of fully evaluated terms, where the `n`-th element
-- is the runtime value bound to the input variable of the function `n` levels up.
-- For example, `[Unit]` means variable `Var 0` has the value `Unit`.
type ValueCtx = [Term]

-- Like the value context, the type context (Γ) is also a stack. Here, the `n`-th
-- is the type of the input variable of the function `n` levels up. For example, `[TUnit]`
-- means variable `Var 0` is of type `TUnit`.
type TypeCtx = [Type]

type TypeErr = String

-- =====

-- Returns either the `n`-th element of a list or an error message.
safeLookup :: [a] -> Int -> String -> Either String a
safeLookup xs n errMsg = case safeHead $ drop n xs of
  Just x  -> Right x
  Nothing -> Left errMsg

-- Either returns the type the term evaluates to, or a type error.
typecheck' :: TypeCtx -> Term -> Either TypeErr Type
typecheck' ctx2 term = case term of
  Unit            -> Right TUnit
  Var n           -> safeLookup ctx2 n (printf "Type of variable %d is not in the ctx. (ctx-depth: %d)" n (length ctx2))
  Lam inType body -> do
    bodyType <- typecheck' (inType : ctx2) body
    return (TFunc inType bodyType)
  Ap fn arg       -> do
    fnType  <- typecheck' ctx2 fn
    argType <- typecheck' ctx2 arg
    case fnType of
      TFunc inType outType
        | argType == inType -> Right outType
        | otherwise         -> Left $ printf "Expected fn argument to be type '%s', but got '%s'" (show inType) (show argType)
      _                     -> Left $ printf "Expected term (%s) to be a function, but got '%s'" (show fnType)

-- Evaluates a term `term` in a value context `ctx1`. The evaluation performs
-- call-by-value beta-reduction. Function applications reduce by substituting the
-- evaluated argument into the lambda body.
eval' :: ValueCtx -> Term -> Either TypeErr Term
eval' ctx1 term = case term of
  Unit              -> Right Unit
  Var n             -> safeLookup ctx1 n (printf "Variable %d is unbound" n)
  Lam inType body   -> Right $ Lam inType body -- Lambdas are values
  Ap fn arg         -> do
    fnVal <- eval' ctx1 fn
    argVal <- eval' ctx1 arg
    case fnVal of
      Lam inType body -> eval' (argVal : ctx1) body
      _               -> Right $ Ap fnVal argVal

typecheck :: Term -> Either TypeErr Type
typecheck = typecheck' []

eval :: Term -> Either TypeErr Term
eval = eval' []

instance Show Term where
  show :: Term -> String
  show t = case t of
    Unit      -> "()"
    (Var n)   -> "x_" ++ show n
    (Lam ty te) -> "\\x_0:" ++ show ty ++ "." ++ showBody te 0
    (Ap fn arg) -> parens fn ++ " " ++ parens arg
    where

    showBody :: Term -> Int -> String
    showBody (Var n)      depth = "x_" ++ show depth
    showBody (Lam _ body) depth = showBody body (depth + 1)
    showBody (Ap fn arg)  depth = showBody fn depth ++ " " ++ showBody arg depth
    showBody Unit         _     = "()"

    parens :: Term -> String
    parens t@(Lam _ _) = "(" ++ show t ++ ")"
    parens t@(Ap _ _)  = "(" ++ show t ++ ")"
    parens t           = show t

instance Show Type where
  show :: Type -> String
  show t = case t of
    TUnit       -> "unit"
    (TFunc a b) -> printf "(%s -> %s)" (show a) (show b)

-- =====

-- λx.x
example1 :: Term
example1 = Lam TUnit (Var 0)

-- (λx.x) Unit
example2 :: Term
example2 = Ap example1 Unit

-- λf.λx.f x
example3 :: Term
example3 = Lam (TFunc TUnit TUnit) (Lam TUnit (Var 0))

test :: (Show a, Eq a) => Either String a -> Either String a -> String -> IO ()
test actual expected name = case (actual, expected) of
  (Right x, Right y)
    | x == y        -> putStrLn $ "[PASS] " ++ name
    | otherwise     -> putStrLn $ "[FAIL] " ++ name ++ ": Expected " ++ show y ++ ", got " ++ show x
  (Left e, Right _) -> putStrLn $ "[FAIL] " ++ name ++ ": Expected success, got error: " ++ e
  (Right _, Left _) -> putStrLn $ "[FAIL] " ++ name ++ ": Expected error, got success"
  _                 -> putStrLn $ "[PASS] " ++ name

main :: IO ()
main = do
  putStrLn "\n=== Examples ==="
  print example1
  print example2
  print example3

  putStrLn "\n=== Type Checking ==="
  test (typecheck example1) (Right $ TFunc TUnit TUnit) "id types as TUnit->TUnit"
  test (typecheck example2) (Right TUnit)               "(id Unit) types as TUnit"

  putStrLn "\n=== Evaluation ==="
  test (eval example1) (Right example1) "identity doesn't reduce"
  test (eval example2) (Right Unit)     "Calling beta-reduces to Unit"
  test (eval example3) (Right Unit)     "double application reduces to Unit"

  putStrLn "\n=== Error Cases ==="
  test (eval (Var 0)) (Left "Variable 0 is unbound") "free variable fails"
