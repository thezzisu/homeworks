module HW5 where

-- Problem #1: define safetail
-- Part #1: use a conditional expression
safetail1 :: [a] -> [a]
safetail1 a = if null a then [] else tail a
-- End Part #1

-- Part #2: use guarded equations
safetail2 :: [a] -> [a]
safetail2 a | null a = []
            | otherwise = tail a
-- End Part #2

-- Part #3: use pattern matching
safetail3 :: [a] -> [a]
safetail3 [] = []
safetail3 (x:xs) = xs
-- End Part #3
-- End Problem #1

-- Problem #2: Luhn algorithm
luhn :: Int -> Int -> Int -> Int -> Bool
luhn a b c d = w `mod` 10 == 0
  where
    w = sum z
    z = map (\a -> if a > 9 then a - 9 else a) y
    y = map (\(a, b) -> if even b then a * 2 else a) x
    x = reverse (zip (reverse [a, b, c, d]) [1..])
-- End Problem #2

-- Problem #3: Caesar crack
-- crack :: String -> String
-- crack xs = encode (-factor) xs
--   where factor = position (minimum chitab) chitab
--         chitab = [chisqr (rotate n table') table | n <- [0..25]]
--         table' = freqs xs
--         freqs = _
--         chisqr = _
-- End Problem #3

-- Problem #4: Pythagorean triples
pyths :: Int -> [(Int, Int, Int)]
pyths n = [(x, y, z) | x <- [1..n], y <- [1..n], z <- [1..n], x * x + y * y == z * z]
-- End Problem #4

-- Problem #5: perfect integers
perfects :: Int -> [Int]
perfects n = [x | x <- [1..n], isPerfect x]
  where
    isPerfect n = n == (sum . factors) n
    factors n = [x | x <- [1..n-1], n `mod` x == 0]
-- End Problem #5

-- Problem #6: scalar product
scalarProduct :: Num a => [a] -> [a] -> a
scalarProduct a b = sum (zipWith (*) a b)
-- End Problem #6
