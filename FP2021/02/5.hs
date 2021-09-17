{-# ANN module "HLint: ignore Use init" #-}

my_init_1 :: [a] -> [a]
my_init_1 arr = take (length arr - 1) arr

my_init_2 :: [a] -> [a]
my_init_2 arr = reverse (tail (reverse arr))

main = do
  let gt = init [1, 9, 2, 6]
  let my = my_init_1 [1, 9, 2, 6]
  print (gt == my)
  let my = my_init_2 [1, 9, 2, 6]
  print (gt == my)
