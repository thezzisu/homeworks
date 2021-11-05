module HW11 where

import Prelude hiding (Maybe (..))

-- Problem #1: Maybe, Foldable and Traversable
data Maybe a = Nothing | Just a
  deriving (Show, Eq, Ord)

instance Functor Maybe where
  fmap f (Just a) = Just $ f a
  fmap _ Nothing = Nothing

instance Foldable Maybe where
  foldMap f (Just a) = f a
  foldMap _ Nothing = mempty

  foldr act init (Just a) = act a init
  foldr act init Nothing = init

  foldl act init (Just a) = act init a
  foldl act init Nothing = init

foldMaybe :: Monoid a => Maybe a -> a
foldMaybe (Just a) = a
foldMaybe Nothing = mempty

instance Traversable Maybe where
  traverse cmap (Just a) = fmap Just (cmap a)
  traverse cmap Nothing = pure Nothing

-- End Problem #1

-- Problem #2: Tree, Foldable and Traversable
data Tree a = Leaf | Node (Tree a) a (Tree a)
  deriving (Show)

instance Functor Tree where
  fmap f Leaf = Leaf
  fmap f (Node l v r) = Node (fmap f l) (f v) (fmap f r)

instance Foldable Tree where
  foldMap f Leaf = mempty
  foldMap f (Node l v r) = foldMap f l <> f v <> foldMap f r
  foldr act init Leaf = init
  foldr act init (Node l v r) = foldr act (v `act` foldr act init r) l
  foldl act init Leaf = init
  foldl act init (Node l v r) = foldl act (foldl act init l `act` v) r

foldTree :: Monoid a => Tree a -> a
foldTree Leaf = mempty
foldTree (Node l v r) = foldTree l <> v <> foldTree r

instance Traversable Tree where
  traverse cmap Leaf = pure Leaf
  traverse cmap (Node l v r) = Node <$> traverse cmap l <*> cmap v <*> traverse cmap r

-- End Problem #2

-- Problem #3: fibonacci using zip/tail/list-comprehension
fibs :: [Integer]
fibs = [0, 1] ++ [x + y | (x, y) <- zip fibs $ tail fibs]

-- End Problem #3

-- Problem #4: Newton's square root
eps :: Double
eps = 0.00001

sqroot :: Double -> Double
sqroot n = let list' = let list = iterate (\a -> (a + n / a) / 2) 1 in takeWhile (\(a, b) -> abs (a - b) > eps) $ zip list $ tail list in snd $ last list'

-- End Problem #4
