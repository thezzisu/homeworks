module HW19 where

-- BMF3-2
tailsums :: Num a => [a] -> [a]
tailsums = reverse . scanr (+) 0
