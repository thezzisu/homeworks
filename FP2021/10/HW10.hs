module HW10 where

import Control.Applicative (Alternative, empty, (<|>))
import Data.Char (isDigit, isLower)

-- Problem #1: Reader Monad
-- 因为 ((->) a) 在标准库中已经实现了 Monad，所以我们使用下面这个新定义的类型代替
newtype Reader a b = Reader {runReader :: a -> b}

instance Functor (Reader a) where
  fmap f (Reader g) = Reader {runReader = f . g}

instance Applicative (Reader a) where
  pure f = Reader {runReader = \x -> f}
  (<*>) (Reader f) (Reader g) = Reader {runReader = \a -> let h = f a; b = g a in h b}

instance Monad (Reader a) where
  (>>=) (Reader f) g = Reader {runReader = \a -> let (Reader s) = g (f a) in s a}

-- End Problem #1

-- Problem #2: Functor, Applicative, Monad
data Expr a
  = Var a
  | Val Int
  | Add (Expr a) (Expr a)
  deriving (Show)

instance Functor Expr where
  fmap f (Var a) = Var (f a)
  fmap f (Val n) = Val n
  fmap f (Add l r) = Add (fmap f l) (fmap f r)

instance Applicative Expr where
  pure f = Var f
  (<*>) _ (Val n) = Val n
  (<*>) vf (Add l r) = Add (vf <*> l) (vf <*> r)
  (<*>) (Var f) (Var a) = Var (f a)
  (<*>) _ (Var a) = undefined

instance Monad Expr where
  (>>=) (Val n) _ = Val n
  (>>=) (Add l r) f = Add (l >>= f) (r >>= f)
  (>>=) (Var a) f = f a

-- End Problem #2

-- Problem #3: Why does factorising the expression grammar make the resulting parser more efficient?
-- Develop-efficient: Decoupling different parsing strategies into sperated functions, which reduces code complexity.
-- Time-efficient   : Using a greedy prefix-matching algorithm, build a AST only cost a liner time complexity.
-- End Problem #3

-- Problem #4: Extend the expression parser
newtype Parser a = P {parse :: String -> [(a, String)]}

instance Functor Parser where
  fmap f p =
    P
      ( \input -> case parse p input of
          [] -> []
          (v, rest) : _ -> [(f v, rest)]
      )

instance Applicative Parser where
  pure f = P (\input -> [(f, input)])
  (<*>) f g =
    P
      ( \input -> case parse f input of
          [] -> []
          (f', input') : _ -> parse (fmap f' g) input'
      )

instance Monad Parser where
  (>>=) f g =
    P
      ( \input -> case parse f input of
          [] -> []
          (a, input') : _ -> parse (g a) input'
      )

instance Alternative Parser where
  empty = P (\input -> [])
  (<|>) p q =
    P
      ( \inp -> case parse p inp of
          [] -> parse q inp
          x -> x
      )

item =
  P
    ( \input ->
        case input of
          [] -> []
          (x : xs) -> [(x, xs)]
    )

sat checker = do
  x <- item
  if checker x
    then return x
    else empty

parseDigit = sat isDigit
parseLower = sat isLower

eval :: String -> Int
eval = fst . head . parse expr

expr :: Parser Int
expr = _

-- End Problem #4
