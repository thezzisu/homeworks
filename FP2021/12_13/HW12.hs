module HW12 where

-- Problem #1: maximum segment sum, the straightforward version
suffixes :: [a] -> [[a]]
suffixes [] = []
suffixes [a] = [[a]]
suffixes x@(_ : xs) = x : suffixes xs

prefixes :: [a] -> [[a]]
prefixes = map reverse . suffixes . reverse

segs :: Num a => [a] -> [[a]]
segs = foldl1 (++) . map suffixes . prefixes

mss :: (Num a, Ord a) => [a] -> a
mss = maximum . map sum . segs

-- End Problem #1

-- Problem #2: maximum segment sum, the smart solution
mssSmart :: (Num a, Ord a) => [a] -> a
mssSmart =
  snd
    . foldl
      ( \(last, ans) cur ->
          let last' = max 0 $ last + cur
              ans' = max ans last'
           in (last', ans')
      )
      (0, 0)

-- End Problem #2
