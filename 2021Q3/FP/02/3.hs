{-# ANN module "HLint: ignore Use last" #-}

my_last_1 :: [a] -> a
my_last_1 arr = head (reverse arr)

main = do
  let gt = last [1, 9, 2, 6]
  let my = my_last_1 [1, 9, 2, 6]
  print (gt == my)