module Main where

import Term
import LTS
import Transform

main :: IO ()
main = do
          putStrLn ""
          let Right e1Term = parseProg "f xs ys p where f = \\xs ys p. case xs of Nil -> Nil | Cons(x,xs) -> case ys of Nil -> Nil | Cons(y,ys) -> Cons((p x y),(f xs ys p))"
              e1LTS = drive e1Term

              Right mapTerm = parseProg "map = \\xs f. case xs of Nil -> Nil | Cons(x,xs) -> Cons(f x, map xs f)"
              mapLTS = drive mapTerm
              Right foldrTerm = parseProg "foldr = \\xs f v. case xs of Nil -> v | Cons(x,xs) -> f x (foldr xs f v)"
              foldrLTS = drive foldrTerm
              Right zipWithTerm = parseProg "zipWith = \\xs ys f. case xs of Nil -> Nil | Cons(x,xs) -> case ys of Nil -> Nil | Cons(y,ys) -> Cons((f x y),(zipWith xs ys f))"
              zipWithLTS = drive zipWithTerm

              Right e2Term = parseProg "f = \\xs x. Cons(x,xs)"
              e2LTS = drive e2Term
              Right e3Term = parseProg "g = \\y ys. Cons(y,ys)"
              e3LTS = drive e3Term

          print (prettyLTS e1LTS)
          print (instanceLTS [] e1LTS zipWithLTS [])
          print (instanceLTS [] e1LTS e2LTS [])