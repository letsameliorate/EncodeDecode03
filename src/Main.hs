module Main where

import Term
import LTS
import Transform

main :: IO ()
main = do
          putStrLn ""
          let Right e = parseProg "f xs ys v where f = \\xs ys v. case xs of Nil -> v | Cons(x,xs) -> case ys of Nil -> v | Cons(y,ys) -> (x * y) + (f xs ys v)"
              l = drive e
              e' = prettyLTS l
          print e