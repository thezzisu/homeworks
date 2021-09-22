frac1 x
  | x == 0 = 1
  | otherwise = x * frac1 (x - 1)

frac2 x = if x == 0 then 1 else x * frac1 (x - 1)
