insert :: Ord a => a  -> [a] -> [a]
insert x [] = [x]
insert x (y : ys)
    | x <= y    = x : y : ys
    | otherwise = y : insert x ys

isort :: Ord a => [a] -> [a]
isort [] = []
isort (x : xs) = insert x (isort xs)

-- 6.1
_and :: [Bool] -> Bool
_and arr = foldl (&&) True arr

_concat :: [[a]] -> [a]
_concat arr = foldl (++) [] arr

_replicate :: Int -> a -> [a]
_replicate n x = map (\_ -> x) [1..n]

_elemAt :: [a] -> Int -> a
_elemAt [] _ = undefined
_elemAt (x : _) 0 = x
_elemAt (_ : xs) n = _elemAt xs (n - 1)

_elem :: Eq a => a -> [a] -> Bool
_elem _ [] = False
_elem x (y: ys) = x == y || _elem x ys

-- 6.2
merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge xa@(x : xs) ya@(y : ys) = if x <= y then x : merge xs ya else y : merge xa ys

-- 6.3
msort :: Ord a => [a] -> [a]
msort [] = []
msort [x] = [x]
msort xs = merge (msort ls) (msort rs)
  where
    len = length xs `div` 2
    ls = take len xs
    rs = drop len xs
