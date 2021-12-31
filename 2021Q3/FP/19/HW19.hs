module HW19 where

-- BMF3-2
tailsums :: Num a => [a] -> [a]
tailsums = reverse . scanr (+) 0

-- The code above is derived from the following:
-- tailsums = fst . foldr (\x (xs, s) -> (xs ++ [x + s], x + s)) ([0], 0)
-- and is more time-efficient.
