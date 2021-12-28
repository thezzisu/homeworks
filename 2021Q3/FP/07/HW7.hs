module HW7 where

-- Problem #1: multiplies for natural numbers
data Nat = Zero | Succ Nat
  deriving (Show)

add :: Nat -> Nat -> Nat
add Zero     n = n
add (Succ m) n = Succ (add m n)

multiplies :: Nat -> Nat -> Nat
multiplies Zero     _ = Zero
multiplies (Succ m) n = add n (multiplies m n)
-- End Problem #1

-- Problem #2: folde for Exprs
data Expr
  = Val Int
  | Add Expr Expr
  | Mul Expr Expr
  deriving (Show)

-- try to figure out the suitable type yourself
folde :: (Int -> Int) -> (Int -> Int -> Int) -> (Int -> Int -> Int) -> Expr -> Int
folde fval fadd fmul (Val a) = fval a
folde fval fadd fmul (Add a b) = fadd (folde fval fadd fmul a) (folde fval fadd fmul b)
folde fval fadd fmul (Mul a b) = fmul (folde fval fadd fmul a) (folde fval fadd fmul b)
-- End Problem #2

-- Problem #3: recursive tree type
data Tree a
  = Leaf a
  | Node (Tree a) (Tree a)
  deriving (Show)
-- End Problem #3
