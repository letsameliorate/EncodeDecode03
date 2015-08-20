module Term where

data Term = Free String
          | Bound Int
          | Lambda String Term
          | Con String [Term]
          | Apply Term Term
          | Fun String
          | Case Term [(String, [String], Term)]
          | Let String Term Term
          | Where Term [(String, Term)]

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