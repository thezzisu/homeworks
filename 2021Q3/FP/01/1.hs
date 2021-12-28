prod :: [Int] -> Int
prod [] = 1
prod (x : rest) = x * prod rest

main = print (prod [2, 3, 4])
