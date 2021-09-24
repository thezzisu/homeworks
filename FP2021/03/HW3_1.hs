module HW3_1 where

-- Problem #1: 写出 and 函数的三种其他的定义
and1 :: Bool -> Bool -> Bool
and1 a b
  | a = b
  | otherwise = a

-- Using Sequences
lAndSeq :: [Bool] -> Bool
lAndSeq [] = True
lAndSeq (x : xs)
  | x = lAndSeq xs
  | otherwise = x

and2 :: Bool -> Bool -> Bool
and2 a b = lAndSeq [a, b]

and3 :: Bool -> Bool -> Bool
and3 a b = if a then b else a
-- End Problem #1

-- Problem #2: 给出函数 div 的一种或多种定义
div1 :: Integer -> Integer -> Integer
div1 x y
  | y < 0 = -div1 x (-y)
  | x < 0 = -div1 (-x) y
  | x < y = 0
  | otherwise = 1 + div (x - y) y

div2 :: Integer -> Integer -> Integer
div2 x y
  | y < 0 = -div2 x (-y)
  | x < 0 = -div2 (-x) y
  | otherwise = fst (last (takeWhile (\(a, b) -> b <= x) (map (\a -> (a, a * y)) [0 ..])))
-- End Problem #2

-- Problem #3: 写出阶乘函数的其他定义：
-- Part #1: 使用条件方程组
factGuard :: Integer -> Integer
factGuard x
  | x == 0 = 1
  | otherwise = x * frac1 (x - 1)
-- End Part #1

-- Part #2: 使用分支表达式
factBranch :: Integer -> Integer
factBranch x = if x == 0 then 1 else x * frac1 (x - 1)
-- End Part #2
-- End Problem #3