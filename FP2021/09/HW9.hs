module Main where

involute :: Int -> Int -> IO ()
involute rest acc = do
  if rest == 0
    then do
      putStr "The total is "
      print acc
      return ()
    else do
      x <- fmap read getLine :: IO Int
      involute (rest - 1) (acc + x)
      return ()

main :: IO ()
main = do
  putStr "How many numbers? "
  n <- fmap read getLine :: IO Int
  involute n 0
  return ()