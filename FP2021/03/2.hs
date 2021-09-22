div1 :: Integer -> Integer -> Integer
div1 x y
  | y < 0 = -div1 x (-y)
  | x < 0 = -div1 (-x) y
  | x < y = 0
  | otherwise = 1 + div (x - y) y

div2 :: Integer -> Integer -> Integer
div2 x y
  | y < 0 = -div2 x (-y)
  | x < 0 = -div2 (-x) y
  | otherwise = fst (last (takeWhile (\(a, b) -> b <= x) (map (\a -> (a, a * y)) [0 ..])))
