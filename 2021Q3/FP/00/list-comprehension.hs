main = do
  let arr = [x ^ 2 | x <- [1 .. 5]]
  print arr
  let arr = [x ^ 2 | x <- [1 .. 5], even x]
  print arr
  let arr = [(x, y) | x <- [1 .. 10], even x, y <- [x .. 10], y `mod` x /= 0]
  print arr

  -- To surpress HLint errors
  print "fin"