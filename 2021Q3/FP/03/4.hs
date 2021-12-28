module Main (main) where {  
  while :: (() -> Bool) -> (() -> [()]) -> [()]
  while cond body
    | cond () = body () ++ while cond body
    | otherwise = []

  main :: IO ();
  main = do {
x <- getStdGen
    putStrLn . show x
  }
}