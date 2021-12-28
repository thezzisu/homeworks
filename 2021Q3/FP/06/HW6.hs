module HW5 where

import Prelude hiding (and, concat, filter, map, elem, (!!))
import Data.Char

-- Problem #1: define prelude functions using recursions
and :: [Bool] -> Bool
and arr = foldl (&&) True arr

concat :: [[a]] -> [a]
concat arr = foldl (++) [] arr

replicate :: Int -> a -> [a]
replicate n x = map (\_ -> x) [1..n]

(!!) :: [a] -> Int -> a
(!!) [] _ = undefined
(!!) (x : _) 0 = x
(!!) (_ : xs) n = (!!) xs (n - 1)

elem :: Eq a => a -> [a] -> Bool
elem _ [] = False
elem x (y: ys) = x == y || elem x ys
-- End Problem #1

-- Problem #2: merge ascending lists
merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge xa@(x : xs) ya@(y : ys) = if x <= y then x : merge xs ya else y : merge xa ys
-- End Problem #2

-- Problem #3: merge sort
msort :: Ord a => [a] -> [a]
msort [] = []
msort [x] = [x]
msort xs = merge (msort ls) (msort rs)
  where
    len = length xs `div` 2
    ls = take len xs
    rs = drop len xs
-- End Problem #3

-- Problem #4: desugar list comprehension using map and filter
theExpr :: (a -> Bool) -> (a -> b) -> [a] -> [b]
-- theExpr p f xs = [f x | x <- xs, p x]
theExpr p f xs = map f $ filter p xs
-- End Problem #4

-- Problem #5: redefine map/filter with foldr
filter :: (a -> Bool) -> [a] -> [a]
filter p = foldr (\x y -> if p x then x : y else y) []

map :: (a -> b) -> [a] -> [b]
map f = foldr (\x y -> f x : y) []
-- End Problem #5

-- Problem #6: error checking for binary string transmitter
type Bit = Int

int2bin :: Int -> [Bit]
int2bin 0 = []
int2bin n = n `mod` 2 : int2bin (n `div` 2)

make8 :: [Bit] -> [Bit]
make8 bits = take 8 (bits ++ repeat 0)

int2bin8 :: Int -> [Bit]
int2bin8 = make8 . int2bin

encodeByte :: [Bit] -> [Bit]
encodeByte payload = payload ++ [sum payload `mod` 2]

encode :: String -> [Bit]
encode = concat . map (encodeByte . make8 . int2bin . ord)

bin2int :: [Bit] -> Int
bin2int = foldr (\x y -> x + 2 * y) 0

decode :: [Bit] -> String
-- modify this line to add error checking
decode = map (chr . bin2int) . map decodeByte . chop

chop :: [Bit] -> [[Bit]]
chop [] = []
chop bits = take 9 bits : chop (drop 9 bits)

decodeByte :: [Bit] -> [Bit]
decodeByte byte =
  if sum payload `mod` 2 == checksum then
    payload
  else
    error("Damn it! Bad checksum.")
  where
    payload = take 8 byte
    checksum = last byte
-- End Problem #6
