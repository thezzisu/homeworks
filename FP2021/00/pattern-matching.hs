not' :: Bool -> Bool
not' True = False
not' False = True

fn x
  | x = False
  | otherwise = True

main = do
  print (fn True)