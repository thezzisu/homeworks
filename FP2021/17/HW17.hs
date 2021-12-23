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
minimax [] = _
