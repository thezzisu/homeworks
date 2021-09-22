import Data.Char

cvtCharInt :: Char -> Int
cvtCharInt c = ord c - ord 'a'

cvtIntChar :: Int -> Char
cvtIntChar i = chr (i + ord 'a')

shiftChar :: Int -> Char -> Char
shiftChar o c
  | isLower c = cvtIntChar ((cvtCharInt c + o) `mod` 26)
  | otherwise = c

shiftStr :: Int -> String -> String
shiftStr o s = [shiftChar o c | c <- s]

main = do
  let str = "haskell is fun"
  let result = shiftStr 3 str
  print result