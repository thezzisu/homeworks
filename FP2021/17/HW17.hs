module HW17 where

lsp :: (a -> Bool) -> [a] -> [a]
lsp p xs = foldl f [] (scanl h [] xs)
  where
    f :: [a] -> [a] -> [a]
    f xs ys = if length xs < length ys then ys else xs

    g :: (a -> Bool) -> [a] -> a -> [a]
    g p xs y = if p y then y : xs else []

    h = g p

minimax :: [[Int]] -> Int    
minimax ((x : xs) : xss) = minimax' (max''' x xs) xss
  where
    minimax' :: Int -> [[Int]] -> Int
    minimax' o [] = o
    minimax' o (xs : xss) = minimax' (min o (max'' o xs)) xss

    max' :: Int -> Int -> [Int] -> Int
    max' o i [] = i
    max' o i (x : xs) = if x >= o then o else max' o (max i x) xs

    max'' :: Int -> [Int] -> Int
    max'' o (x : xs) = if x >= o then o else max' o x xs

    max''' :: Int -> [Int] -> Int
    max''' i [] = i
    max''' i (x : xs) = max''' (max i x) xs
