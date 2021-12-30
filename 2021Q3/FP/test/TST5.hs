module TST5 where

foldl' :: (a -> b -> a) -> a -> [b] -> a
foldl' f e arr = foldr (\x g a -> g (f a x)) id arr e

foldr' :: (a -> b -> b) -> b -> [a] -> b
foldr' f e arr = foldl (\g x a -> g (f x a)) id arr e