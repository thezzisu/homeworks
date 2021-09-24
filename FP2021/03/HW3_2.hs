-- 猜数字小游戏
module Main where

import System.Random

generateX :: IO Int
generateX = do
  x <- randomRIO (1, 10)
  return x

while :: IO Bool -> IO () -> IO ()
while cond action = do
  c <- cond
  if c then do
    action
    while cond action
  else return ()

readInt :: IO Int
readInt = do
  line <- getLine
  return (read line :: Int)

check :: Int -> IO Bool
check x = do
  putStrLn "请输入你猜的数字："
  y <- readInt
  if y < x then do
    putStrLn "猜小了"
    return True
  else if y > x then do
    putStrLn "猜大了"
    return True
  else do
    putStrLn "猜对了"
    return False

main :: IO ()
main = do
  x <- generateX
  -- print x
  while (check x) (return ())
