module HW19 where

-- BMF3-2
tailsums :: Num a => [a] -> [a]
tailsums = fst . foldr (\x (xs, s) -> (xs ++ [x + s], x + s)) ([0], 0)

-- Anyway, the following will probably be faster:
-- tailsums = reverse . scanr (+) 0
