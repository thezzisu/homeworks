{-# LANGUAGE ForeignFunctionInterface #-}

foreign import ccall "exp" c_exp :: Double -> Double

foreign import ccall "sqrt" c_sqrt :: Double -> Double

main = do
  print (sqrt 100.0)