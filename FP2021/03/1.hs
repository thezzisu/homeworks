-- Using Guards
lAnd1 :: Bool -> Bool -> Bool
lAnd1 a b
  | a = b
  | otherwise = a

-- Using Sequences
lAndSeq :: [Bool] -> Bool
lAndSeq [] = True
lAndSeq (x : xs)
  | x = lAndSeq xs
  | otherwise = x

lAnd2 :: Bool -> Bool -> Bool
lAnd2 a b = lAndSeq [a, b]

-- Using if-else clause
lAnd3 :: Bool -> Bool -> Bool
lAnd3 a b = if a then b else a
