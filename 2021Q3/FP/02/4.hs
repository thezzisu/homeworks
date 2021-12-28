{-# ANN module "HLint: ignore Use last" #-}

my_last_2 :: [a] -> a
my_last_2 arr = arr !! (length arr - 1)

main = do
  let gt = last [1, 9, 2, 6]
  let my = my_last_2 [1, 9, 2, 6]
  print (gt == my)