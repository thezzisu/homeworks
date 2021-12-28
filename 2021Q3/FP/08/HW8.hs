module HW8 where

-- 为简便起见，我们不允许任何中间结果超出 2^31。
-- 这意味着可以提前对搜索进行剪枝：
-- 1. 任何结果均不允许超过 2^32。
-- 2. 任何指数均不允许超过 32。
-- 在大家的 64 位系统上，GHC 一般把 Int 实现为 64 位整数，因此
-- 只要严格执行上述剪枝策略，就不必担心运算溢出问题。

data Op
  = Add
  | Sub
  | Mul
  | Div
  | Exp
  deriving (Eq)

data Expr
  = Val Int
  | App Op Expr Expr
  deriving (Eq)

-- 你需要完成下面的 solutions 函数

type Result = (Expr, Int)

limit :: Int
limit = 2 ^ 31

apply :: Op -> Int -> Int -> Int
apply Add x y = x + y
apply Sub x y = x - y
apply Mul x y = x * y
apply Div x y = x `div` y
apply Exp x y = x ^ y

valid :: Op -> Int -> Int -> Bool
valid Add x y = x <= y && x + y <= limit
valid Sub x y = x > y
valid Mul x y = x <= y && x /= 1 && y /= 1 && x * y <= limit
valid Div x y = x `mod` y == 0 && y /= 1
valid Exp x y =
  y /= 1
    && y <= 31
    && y <= ceiling (logBase (fromIntegral x) (fromIntegral limit))
    && x ^ y <= limit

eval :: Expr -> [Int]
eval (Val n) = [n | n > 0]
eval (App o l r) = [apply o x y | x <- eval l, y <- eval r, valid o x y]

subs :: [a] -> [[a]]
subs [] = [[]]
subs (x : xs) = yss ++ map (x :) yss where yss = subs xs

interleave :: a -> [a] -> [[a]]
interleave x [] = [[x]]
interleave x (y : ys) = (x : y : ys) : map (y :) (interleave x ys)

perms :: [a] -> [[a]]
perms = foldr (concatMap . interleave) [[]]

choices :: [a] -> [[a]]
choices = concatMap perms . subs

split :: [a] -> [([a], [a])]
split [] = []
split [_] = []
split (x : xs) = ([x], xs) : [(x : a, b) | (a, b) <- split xs]

combine :: Result -> Result -> [Result]
combine (l, x) (r, y) = [(App op l r, apply op x y) | op <- [Add, Sub, Mul, Div, Exp], valid op x y]

results :: [Int] -> [Result]
results [] = []
results [n] = [(Val n, n) | n > 0]
results ns = [r | (ls, rs) <- split ns, lr <- results ls, rr <- results rs, r <- combine lr rr]

tryments :: [Int] -> [Result]
tryments ns = [result | ms <- choices ns, result <- results ms]

-- solutions :: [Int] -> Int -> [Expr]
-- solutions ns n = [expr | (expr, val) <- tryments ns, val == n]

fucker :: [Result] -> Int -> Int -> (Int, [Expr])
fucker [] n best = (limit, [])
fucker (now : rest) n prefixBest = if currentOffset <= suffixBest && currentOffset <= prefixBest then (suffixBest, fst now : snd next) else (suffixBest, snd next)
  where
    currentOffset = abs (snd now - n)
    suffixBest = min currentOffset (fst next)
    next = fucker rest n (min currentOffset prefixBest)

solutions :: [Int] -> Int -> [Expr]
solutions ns n = snd (fucker (tryments ns) n limit)

-- 下面是我们为 Expr 和 Op 提供的一个 Show 的实现
-- 这并不是本次作业必需的，但是在调试过程中可能会让表达式更易读
-- 这个实现使用了 showsPrec，有关它的细节你可以参考相关文档：
-- https://hackage.haskell.org/package/base-4.15.0.0/docs/Text-Show.html#t:Show
-- 以及 Haskell 2010 Report 的 11.4 节：
-- https://www.haskell.org/onlinereport/haskell2010/haskellch11.html

instance Show Op where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"
  show Exp = "^"

-- 提示：指数运算可以显示为 x ^ y

instance Show Expr where
  showsPrec _ (Val n) = shows n
  showsPrec p (App op x y) =
    showParen (p > q) $
      showsPrec q x . showChar ' ' . shows op
        . showChar ' '
        . showsPrec (succ q) y
    where
      q = case op of
        Add -> 6
        Sub -> 6
        Mul -> 7
        Div -> 7
        Exp -> 8

-- 提示：给出指数运算的优先级
-- 可以参考Haskell定义的优先级（:info ^）