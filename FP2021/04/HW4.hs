module HW4 where

-- Problem #1: 补全下列值的类型签名
val1 :: [Char]
val1 = ['a', 'b', 'c']

val2 :: (Char, Char, Char)
val2 = ('a', 'b', 'c')

val3 :: [(Bool, Char)]
val3 = [(False, '0'), (True, '1')]

val4 :: ([Bool], [Char])
val4 = ([False, True], ['0', '1'])

val5 :: [[a] -> [a]]
val5 = [tail, init, reverse]
-- End Problem #1

-- Problem #2: 补全下列函数的类型签名
second :: [a] -> a
second xs = head (tail xs)

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

pair :: a -> b -> (a, b)
pair x y = (x, y)

double :: Num a => a -> a
double x = x * 2

palindrome :: Eq a => [a] -> Bool
palindrome xs = reverse xs == xs

twice :: (a -> a) -> a -> a
twice f x = f (f x)
-- End Problem #2

-- Problem #3: Int/Integer，show/read
-- Part #1: Int/Integer的区别
-- < a = 1 :: Int
-- < b = 1 :: Integer
-- < :type a
-- > a :: Int
-- < :type b
-- > b :: Integer
-- < a == b
-- > <interactive>:5:6: error:
-- >     • Couldn't match expected type ‘Int’ with actual type ‘Integer’
-- >     • In the second argument of ‘(==)’, namely ‘b’
-- >       In the expression: a == b
-- >       In an equation for ‘it’: it = a == b
-- End Part #1

-- Part #2: show/read的用法
--   (Continue the above example)
--   < :type show
--   > show :: Show a => a -> String
--   < :type read
--   > read :: Read a => String -> a
--   < show a
--   > "1"
--   < read "1" :: Int
--   > 1
--   < read "1" :: Double
--   > 1.0
-- End Part #2
-- End Problem #3

-- Problem #4: Integral/Fractional
-- Part #1: Integral
--   请把你的答案填写在这里（可以考虑直接复制命令行窗口的内容）
-- 示例：
--   Prelude> 你输入的表达式
--   GHCi返回的结果
-- End Part #1

-- Part #2: Fractional
--   请把你的答案填写在这里（可以考虑直接复制命令行窗口的内容）
-- 示例：
--   Prelude> 你输入的表达式
--   GHCi返回的结果
-- End Part #2
-- End Problem #3
