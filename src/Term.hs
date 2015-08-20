module Term where

import Data.Char
import Data.Maybe
import Data.List (intersect,(\\))
import Data.Foldable (foldrM,find)
import Control.Monad
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language

data Term = Free String
          | Bound Int
          | Lambda String Term
          | Con String [Term]
          | Apply Term Term
          | Fun String
          | Case Term [(String, [String], Term)]
          | Let String Term Term
          | Where Term [(String, Term)]

instance Show Term where
   show t = render (prettyTerm t)

instance Eq Term where
   (==) (Free x) (Free x') = x==x'
   (==) (Bound i) (Bound i') = i==i'
   (==) (Lambda x t) (Lambda x' t') = t==t'
   (==) (Con c ts) (Con c' ts') = c==c' && ts==ts'
   (==) (Apply t u) (Apply t' u') = t==t' && u==u'
   (==) (Fun f) (Fun f') = f==f'
   (==) u@(Case t bs) u'@(Case t' bs') | match u u' = t==t' && (all (\ ((c,xs,t),(c',xs',t')) -> t==t') (zip bs bs'))
   (==) (Let x t u) (Let x' t' u') = t==t' && u==u'
   (==) (Where t ds) (Where t' ds') = t==t' && ds==ds'
   (==) t t' = False

match (Free x) (Free x') = x==x'
match (Bound i) (Bound i') = i==i'
match (Lambda x t) (Lambda x' t') = True
match (Con c ts) (Con c' ts') = c==c' && length ts == length ts'
match (Apply t u) (Apply t' u') = True
match (Fun f) (Fun f') = f==f'
match (Case t bs) (Case t' bs') = (length bs == length bs') && (all (\((c,xs,t),(c',xs',t')) -> c == c' && length xs == length xs') (zip bs bs'))
match (Let x t u) (Let x' t' u') = True
match (Where t ds) (Where t' ds') = ds == ds'
match t t' = False

free t = free' [] t

free' xs (Free x) = if (x `elem` xs) then xs else x:xs
free' xs (Bound i) = xs
free' xs (Lambda x t) = free' xs t
free' xs (Con c ts) = foldr (\t xs -> free' xs t) xs ts
free' xs (Apply t u) = free' (free' xs t) u
free' xs (Fun f) = xs
free' xs (Case t bs) = foldr (\(c,xs,t) xs' -> free' xs' t) (free' xs t) bs
free' xs (Let x t u) = free' (free' xs t) u
free' xs (Where t ds) = foldr (\(x,t) xs -> free' xs t) (free' xs t) ds

embed t u = couple t u []

embedding t u s = mplus (couple t u s) (dive t u s)

couple (Free x) (Free x') s = if x `elem` fst (unzip s)
                              then if (x,x') `elem` s then Just s else Nothing
                              else Just ((x,x'):s)
couple (Bound i) (Bound i') s | i == i' = Just s
couple (Lambda _ t) (Lambda _' t') s = embedding t t' s
couple u@(Con c' ts) u'@(Con c'' ts') s | match u u' = foldrM (\ (t,t') s -> embedding t t' s) s (zip ts ts')
couple (Apply t u) (Apply t' u') s | match t t' = (embedding t t' s) >>= (embedding u u')
couple (Fun f) (Fun f') s | f==f' = Just s
couple u@(Case t bs) u'@(Case t' bs') s | match u u' = (embedding t t' s) >>= (\s->foldrM (\ ((_,_,t),(_,_,t')) s -> embedding t t' s) s (zip bs bs'))
couple (Let _ t u) (Let _ t' u') s = (embedding t t' s) >>= (embedding u u')
couple (Where t ds') (Where t' ds'') s = let (vs,ts) = unzip ds'
                                             (vs',ts') = unzip ds''
                                         in (embedding t t' s) >>= (\s -> foldrM (\(t,t') s -> embedding t t' s) s (zip ts ts'))

couple t u s = Nothing

dive t (Lambda x t') s = embedding t t' s
dive t (Con c ts) s = msum (map (\t' -> embedding t t' s) ts)
dive t (Apply t' u) s = mplus (embedding t t' s) (embedding t u s)
dive t (Case t' bs) s = mplus (embedding t t' s) (msum (map (\(_,vs,t') -> embedding t (shift (length vs) 0 t') s) bs))
dive t (Let x t' u) s = mplus (embedding t t' s) (embedding t u s)
dive t (Where t' ds') s = embedding t t' s
dive t u s = Nothing

shift 0 d u = u
shift i d (Free x) = Free x
shift i d (Bound j) = if j >= d then Bound (j+i) else Bound j
shift i d (Lambda x t) = Lambda x (shift i (d+1) t)
shift i d (Con c ts) = Con c (map (shift i d) ts)
shift i d (Apply t u) = Apply (shift i d t) (shift i d u)
shift i d (Fun f) = Fun f
shift i d (Case t bs) = Case (shift i d t) (map (\(c,xs,t) -> (c,xs,shift i (d+length xs) t)) bs)
shift i d (Let x t u) = Let x (shift i d t) (shift i (d+1) u)
shift i d (Where t ds) = Where (shift i d t) (map (\(x,t) -> (x,shift i d t)) ds)

subst t u = subst' 0 t u

subst' i t (Free x) = Free x
subst' i t (Bound i') = if   i'<i
                        then Bound i'
                        else if   i'==i
                             then shift i 0 t
                             else Bound (i'-1)
subst' i t (Lambda x t') = Lambda x (subst' (i+1) t t')
subst' i t (Con c ts) = Con c (map (subst' i t) ts)
subst' i t (Apply t' u) = Apply (subst' i t t') (subst' i t u)
subst' i t (Fun f) = Fun f
subst' i t (Case t' bs) = Case (subst' i t t') (map (\(c,xs,u) -> (c,xs,subst' (i+length xs) t u)) bs)
subst' i t (Let x t' u) = Let x (subst' i t t') (subst' (i+1) t u)
subst' i t (Where t' ds) = Where (subst' i t t') (map (\(x,u) -> (x,subst' i t u)) ds)

instantiate s t = instantiate' 0 s t

instantiate' d s (Free x) = case (lookup x s) of
                               Just t  -> shift d 0 t
                               Nothing -> Free x
instantiate' d s (Bound i) = Bound i
instantiate' d s (Lambda x t) = Lambda x (instantiate' (d+1) s t)
instantiate' d s (Con c ts) = Con c (map (instantiate' d s) ts)
instantiate' d s (Apply t u) = Apply (instantiate' d s t) (instantiate' d s u)
instantiate' d s (Fun f) = Fun f
instantiate' d s (Case t bs) = Case (instantiate' d s t) (map (\(c,xs,t) -> (c,xs,instantiate' (d+length xs) s t)) bs)
instantiate' d s (Let x t u) = Let x (instantiate' d s t) (instantiate' (d+1) s u)
instantiate' d s (Where t ds) = Where (instantiate' d s t) (map (\(x,t) -> (x,instantiate' d s t)) ds)

abstract x t = abstract' 0 x t

abstract' i x (Free x') = if x==x' then Bound i else Free x'
abstract' i x (Bound i') = if i'>=i then Bound (i'+1) else Bound i'
abstract' i x (Lambda x' t) = Lambda x' (abstract' (i+1) x t)
abstract' i x (Con c ts) = Con c (map (abstract' i x) ts)
abstract' i x (Apply t u) = Apply (abstract' i x t) (abstract' i x u)
abstract' i x (Fun f) = Fun f
abstract' i x (Case t bs) = Case (abstract' i x t) (map (\(c,xs,t) -> (c,xs,abstract' (i + length xs) x t)) bs)
abstract' i x (Let x' t u) = Let x' (abstract' i x t) (abstract' (i+1) x u)
abstract' i x (Where t ds) = Where (abstract' i x t) (map (\(x',t) -> (x',abstract' i x t)) ds)

rename fv x = if   x `elem` fv
              then rename fv (x++"'")
              else x

stripLambda (Lambda x t) = let x' = rename (free t) x
                               (xs,u) = stripLambda (subst (Free x') t)
                           in  (x':xs,u)
stripLambda t = ([],t)

blank = Text.PrettyPrint.HughesPJ.space

prettyTerm (Free x) = text x
prettyTerm (Bound i) = (text "#") <> (int i)
prettyTerm t@(Lambda _ _) = let (xs,t') = stripLambda t
                            in  (text "\\") <> (hsep (map text xs)) <> (text ".") <> (prettyTerm t')
prettyTerm t@(Con c ts) = if   isNat t
                          then int (con2nat t)
                          else if isList t
                               then text "[" <> (hcat (punctuate comma (map prettyTerm (con2list t)))) <> (text "]")
                               else if ts==[]
                                    then text c
                                    else (text c) <> (parens (hcat (punctuate comma (map prettyTerm ts))))
prettyTerm t@(Apply _ _) = prettyApp t
prettyTerm (Fun f) = text f
prettyTerm (Case t (b:bs)) = hang ((text "case") <+> (prettyAtom t) <+> (text "of")) 1 (blank <+> (prettyBranch b) $$ (vcat (map (\b->(text "|" <+>) (prettyBranch b)) bs))) where
   prettyBranch (c,[],t) = (text c) <+> (text "->") <+> (prettyTerm t)
   prettyBranch (c,xs,t) = let fv = foldr (\x fv -> let x' = rename fv x in x':fv) (free t) xs
                               xs' = take (length xs) fv
                               t' = foldr (\x t->subst (Free x) t) t xs'
                           in  (text c) <> (parens (hcat (punctuate comma (map text xs')))) <+> (text "->") <+> (prettyTerm t') $$ empty
prettyTerm (Let x t u) = let x' = rename (free u) x
                         in  ((text "let") <+> (text x') <+> (text "=") <+> (prettyTerm t)) $$ ((text "in") <+> (prettyTerm (subst (Free x') u)))
prettyTerm (Where t ds) = (prettyTerm t) $$ (text "where") $$ (prettyEnv ds)

prettyApp (Apply t u) = (prettyApp t) <+> (prettyAtom u)
prettyApp t = prettyAtom t

prettyAtom (Free x) = text x
prettyAtom t@(Con c ts) = if   isNat t
                          then int (con2nat t)
                          else if isList t
                               then text "[" <> (hcat (punctuate comma (map prettyTerm  (con2list t)))) <> (text "]")
                               else if ts==[]
                                    then text c
                                    else (text c) <> (parens (hcat (punctuate comma (map prettyTerm ts))))
prettyAtom (Fun f) = text f
prettyAtom t = parens (prettyTerm t)

prettyEnv [(x,t)] = (text x) <+> equals <+> (prettyTerm t)
prettyEnv ((x,t):ds) = (text x) <+> equals <+> (prettyTerm t) <> semi $$ (prettyEnv ds)

isList (Con "Nil" []) = True
isList (Con "Cons" [h,t]) = isList t
isList _ = False

list2con [] = Con "Nil" []
list2con (h:t) = Con "Cons" [h,list2con t]

con2list (Con "Nil" [])  = []
con2list (Con "Cons" [h,t]) = h:con2list t

isNat (Con "Zero" []) = True
isNat (Con "Succ" [n]) = isNat n
isNat _ = False

nat2con 0 = Con "Zero" []
nat2con n = Con "Succ" [nat2con (n-1)]

con2nat (Con "Zero" [])  = 0
con2nat (Con "Succ" [n]) = 1+con2nat n

potDef = emptyDef
         { commentStart    = "/*"
         , commentEnd      = "*/"
         , commentLine     = "--"
         , nestedComments  = True
         , identStart      = lower
         , identLetter     = do alphaNum <|> oneOf "_'"
         , reservedNames   = ["case","of","where","ALL","EX","ANY"]
         , reservedOpNames = ["~","/\\","\\/","<=>","=>"]
         , caseSensitive   = True
         }

lexer = T.makeTokenParser potDef

symbol     = T.symbol lexer
bracks     = T.parens lexer
semic      = T.semi lexer
comm       = T.comma lexer
identifier = T.identifier lexer
reserved   = T.reserved lexer
reservedOp = T.reservedOp lexer
natural    = T.natural lexer

con = do
      c <- upper
      cs <- many (do alphaNum <|> oneOf "_'")
      return (c:cs)

makeWhere t [] = t
makeWhere t fs = let (fn,_) = unzip fs
                 in  makeFuns fn (Where t fs)

makeFuns fn (Free x) = if x `elem` fn then Fun x else Free x
makeFuns fn (Bound i ) = Bound i
makeFuns fn (Lambda x t) = Lambda x (makeFuns fn t)
makeFuns fn (Con c ts) = Con c (map (makeFuns fn) ts)
makeFuns fn (Apply t u) = Apply (makeFuns fn t) (makeFuns fn u)
makeFuns fn (Fun f) = Fun f
makeFuns fn (Case t bs) = Case (makeFuns fn t) (map (\(c,xs,t) -> (c,xs,makeFuns fn t)) bs)
makeFuns fn (Let x t u) = Let x (makeFuns fn t) (makeFuns fn u)
makeFuns fn (Where t ds) = Where (makeFuns fn t) (map (\(x,t) -> (x,makeFuns fn t)) ds)

prog = do
       e <- expr
       fs <-     do
                 reserved "where"
                 fs <- sepBy1 fundef semic
                 return fs
             <|> do
                 spaces
                 return []
       return (makeWhere e fs)

fundef = do
         f <- identifier
         symbol "="
         e <- expr
         return (f,e)

expr = buildExpressionParser prec term

prec = [ [ unop "~" (Fun "not")],
         [ op "+" (Fun "plus") AssocRight ],
         [ op "-" (Fun "minus") AssocRight ],
         [ op "*" (Fun "mult") AssocRight ],
         [ op "/" (Fun "div") AssocRight ],
         [ op "/\\" (Fun "and") AssocRight ],
         [ op "\\/" (Fun "or") AssocRight ],
         [ op "<=>" (Fun "iff") AssocRight ],
         [ op "=>" (Fun "implies") AssocRight ]
       ]
       where
       op o t assoc   = Infix (do
                               reservedOp o
                               return (\x y -> Apply (Apply t x) y)
                              ) assoc
       unop o t       = Prefix (do
                                reservedOp o
                                return (\x -> Apply t x)
                               )

term =     do
           f <- atom
           as <- many atom
           return (foldl Apply f as)
       <|> do
           symbol "\\"
           xs <- many1 identifier
           symbol "."
           e <- expr
           return (foldr (\x t->Lambda x (abstract x t)) e xs)
       <|> do
           reserved "case"
           e <- expr
           reserved "of"
           bs <- sepBy1 branch (symbol "|")
           return (Case e bs)

atom =     do
           x <- identifier
           return (Free x)
       <|> do
           c <- con
           es <-     do
                     es <- bracks (sepBy1 expr comm)
                     return es
                 <|> do
                     spaces
                     return []
           return (Con c es)
       <|> do
           n <- natural
           return (nat2con n)
       <|> do
           symbol "["
           ts <- sepBy expr comm
           symbol "]"
           return (list2con ts)
       <|> do
           e <- bracks expr
           return e

branch = do
         c <- con
         xs <-     do
                   xs <- bracks (sepBy1 identifier comm)
                   return xs
               <|> do
                   spaces
                   return []
         symbol "->"
         e <- expr
         return (c,xs,foldl (\t x -> abstract x t) e xs)

parseExpr input = parse expr "(ERROR)" input

parseProg input = parse prog "(ERROR)" input
