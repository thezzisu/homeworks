module HW5 where
import Data.Char

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
isChar :: Char -> Bool
isChar c = ord c >= ord 'a' && ord c <= ord 'z'
charToInt :: Char -> Int
charToInt c = ord c - ord 'a'
intToChar :: Int -> Char
intToChar n = chr (ord 'a' + n)

encode :: Int -> [Char] -> [Char]
encode n xs = [ if isChar x then shift n x else x | x <- xs ]
shift :: Int -> Char -> Char
shift n c = intToChar ((charToInt c + n) `mod` 26)
table :: [Float]
table = [8.1, 1.5, 2.8, 4.2, 12.7, 2.2, 2.0, 6.1, 7.0, 0.2, 0.8, 4.0, 2.4, 6.7, 7.5, 1.9, 0.1, 6.0, 6.3, 9.0, 2.8, 1.0, 2.4, 0.2, 2.0, 0.1]

crack :: String -> String
crack xs = encode (-factor) xs
  where factor = position (minimum chitab) chitab
        chitab = [chisqr (rotate n freqs) table | n <- [0..25]]
        rotate n arr = drop n arr ++ take n arr
        freqs = map (\x -> charCount x / xsCount) [0..25]
        charCount c = fromIntegral (length (filter (\y -> charToInt y == c) xs)) :: Float
        xsCount = fromIntegral (length (filter isChar xs)) :: Float
        chisqr a b = sum (zipWith (\x y -> (x - y) * (x - y) / y) a b)
        position a arr = head (positions a arr)
        positions a arr = map snd $ filter (\(x, y) -> x == a) (zip arr [0..25])
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
