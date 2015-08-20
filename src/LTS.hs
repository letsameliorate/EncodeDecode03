module LTS where

import Term
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language

data LTS = Node Term [LTS]
         | Unfold String Term LTS
         | ConElim String Term LTS
         | Function String LTS
         | Var String LTS
         | Embedding String LTS

instance Show LTS where
   show t = render (prettyLTS t)

instance Eq LTS where
   (==) l l' = eqLTS [] l l'

eqLTS c (Node t ls) (Node t' ls') | match t t' = all (\ (l,l') -> eqLTS c l l') (zip ls ls')
eqLTS c (Unfold f t l) (Unfold f' t' l') | f==f' = eqLTS c l l'
eqLTS c l (Unfold _ _ l') = eqLTS c l l'
eqLTS c (ConElim c' _ l) (ConElim c'' _ l') | c'==c'' = eqLTS c l l'
eqLTS c l (ConElim _ _ l') = eqLTS c l l'
eqLTS c (Function f l) (Function f' l') = eqLTS ((f,f'):c) l l'
eqLTS c (Var x l) (Var x' l') = eqLTS c l l'
eqLTS c (Embedding f l) (Embedding f' l') = (f,f') `elem` c
eqLTS c l l' = False

freeLTS l = freeLTS' [] l

freeLTS' xs (Node (Free x) []) = if x `elem` xs then xs else x:xs
freeLTS' xs (Node t ls) = foldr (\l xs -> freeLTS' xs l) xs ls
freeLTS' xs (Unfold f t l) = freeLTS' xs l
freeLTS' xs (ConElim c _ l) = freeLTS' xs l
freeLTS' xs (Function f l) = freeLTS' xs l
freeLTS' xs (Var x l) = freeLTS' xs l
freeLTS' xs (Embedding f l) = xs

substLTS l l' = substLTS' 0 l l'
substLTS' i l (Node (Free x') []) = Node (Free x') []
substLTS' i l (Node (Bound i') []) = if   i'<i
                                     then Node (Bound i') []
                                     else if   i'==i
                                          then l
                                          else Node (Bound (i'-1)) []
substLTS' i l (Node (Lambda x t) [l']) = Node (Lambda x t) [substLTS' (i+1) l l']
substLTS' i l (Node (Case t bs) (l':ls)) = Node (Case t bs) ((substLTS' i l l'):(map (\((c,xs,t),l') -> substLTS' (i+length xs) l l')) (zip bs ls))
substLTS' i l (Node (Let x t u) [l',l'']) = Node (Let x t u) [substLTS' i l l',substLTS' (i+1) l l'']
substLTS' i l (Node t ls) = Node t (map (substLTS' i l) ls)
substLTS' i l (Unfold f t l') = Unfold f t (substLTS' i l l')
substLTS' i l (ConElim c t l') = ConElim c t (substLTS' i l l')
substLTS' i l (Function f l') = Function f (substLTS' i l l')
substLTS' i l (Embedding f l') = Embedding f (substLTS' i l l')

stripAbs (Node (Lambda x t) [l]) = let x' = rename (freeLTS l) x
                                       (xs,l') = stripAbs (substLTS (Node (Free x') []) l)
                                   in  (x':xs,l')
stripAbs l = ([],l)

prettyLTS (Node (Free x) []) = text x
prettyLTS (Node (Bound i) []) = (text "#") <> (int i)
prettyLTS l@(Node (Lambda _ _) _) = let (xs,l') = stripAbs l
                                    in  (text "\\") <> (hsep (map text xs)) <> (text ".") <> (prettyLTS l')
prettyLTS (Node (Con c _) ls) = if ls==[] then text c
                                          else (text c) <> (parens (hcat (punctuate comma (map prettyLTS ls))))
prettyLTS (Node (Apply _ _) [l,l']) = (prettyLTS l) <+> (prettyLTS l')
prettyLTS (Node (Case t (b:bs)) (l:l':ls)) = hang ((text "case") <+> (prettyArg l) <+> (text "of")) 1 (blank <+> (prettyBranch (b,l')) $$ (vcat (map (\(b,l) -> (text "|" <+>) (prettyBranch (b,l))) (zip bs ls)))) where
   prettyBranch ((c,[],t),l) = (text c) <+> (text "->") <+> (prettyLTS l)
   prettyBranch ((c,xs,t),l) = let fv = foldr (\x fv -> let x' = rename fv x in x':fv) (freeLTS l) xs
                                   xs' = take (length xs) fv
                                   l' = foldr (\x l -> substLTS (Node (Free x) []) l) l xs'
                               in  (text c) <> (parens (hcat (punctuate comma (map text xs')))) <+> (text "->") <+> (prettyLTS l') $$ empty
prettyLTS (Node (Let x t u) [l,l']) = let x' = rename (freeLTS l') x
                                      in   ((text "let") <+> (text x') <+> (text "=") <+> (prettyLTS l)) $$ ((text "in") <+> (prettyLTS (substLTS (Node (Free x') []) l')))
prettyLTS (Unfold f t l) = (text ("-"++f++"->")) <+> (prettyLTS l)
prettyLTS (ConElim c _ l) = (text ("-"++c++"->")) <+> (prettyLTS l)
prettyLTS (Function f l) = (text (f++":")) <+> (prettyLTS l)
prettyLTS (Var x l) = (text (x++":")) <+> (prettyLTS l)
prettyLTS (Embedding f l) = text f

prettyArg (Node (Free x) []) = text x
prettyArg (Node (Bound i) []) = (text "#") <> (int i)
prettyArg (Node (Con c _) ls) = if ls==[] then text c
                                          else (text c) <> (parens (hcat (punctuate comma (map prettyLTS ls))))
prettyArg l = parens (prettyLTS l)
