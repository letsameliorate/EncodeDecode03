module Main where

import Term
import LTS
import Transform

main :: IO ()
main = do
          putStrLn ""
          let Right e = parseProg ""
              l = drive e
              e' = prettyLTS l
          print e