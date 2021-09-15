qs :: [Int] -> [Int]
qs [] = []
qs (x : list) = qs left ++ [x] ++ qs right
  where
    left = filter (> x) list
    right = filter (<= x) list

main = print (qs [1, 4, 2, 3, 5])