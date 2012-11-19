module TermManip where

import           Control.Monad.State
import           Data.List           (intersperse)
import           Debug.Trace         (trace)

data Term = App Term Term
          | Var String
          | List [Term]
          deriving Show

ppPrec :: Int -> Term -> String
ppPrec _ (List ts) = "[" ++ (concat . intersperse ", " . map pp $ ts) ++ "]"
ppPrec _ (Var s) = s
ppPrec p (App l r) = parensIf (p > 1) $ ppPrec 0 l ++ " " ++ ppPrec 2 r
  where
    parensIf True p = "(" ++ p ++ ")"
    parensIf False p = p

pp :: Term -> String
pp = ppPrec 0

testTerm = App (App (App (Var "g") (List [App (Var "f") (Var "x"), App (Var "f") (Var "y")])) (App (Var "f") (Var "y"))) (Var "f")
testTerm' = App (App (App (Var "g") (List [App (Var "h") (Var "x"), App (Var "h") (Var "y")])) (App (Var "f") (Var "y"))) (Var "f")

collectArgs :: Term -> Bool -> [Term] -> [(String, [Term])]
collectArgs (Var s) left args = if left
                                then [(s, reverse args)]
                                else []
collectArgs (List ts) left args = if left
                                  then error "ehh, doesn't typecheck"
                                  else concatMap (\t -> collectArgs t False []) ts
collectArgs (App l r) _ args = collectArgs l True (args ++ [r]) ++ collectArgs r False []

testArgs :: Term -> [(String, [String])]
testArgs t = map (\(s,a) -> (s, map pp a)) $ collectArgs t False []

count :: String -> Term -> Term
count recFunName t = let (t',_,_) = count' 0 t True
                     in t'
  where
    count' n t@(Var str) isRight
      | isRight && recFunName == str = ( (App t (Var ("h" ++ show n)))
                                     , n + 1
                                     , True
                                     )
      | recFunName == str           = ( t
                                     , n + 1
                                     , True
                                     )
      | otherwise                  = (t,n,False)
    count' n t@(List ts) isRight   = if not isRight
                                     then error "count: term does not typecheck."
                                     else let (n', t') = sequence' n ts
                                          in (List t', n', False)
      where
        sequence' n []     = (n, [])
        sequence' n (x:xs) = let (t', n', b) = count' n x True
                             in (if b then n'+1 else n', t' : snd (sequence' n' xs))
    count' n t@(App l r) isRight
      | isRight && b                = ( (App (App l' r') (Var ("h" ++ show n)))
                                     , n''
                                     , b
                                     )
      | otherwise                  = (App l' r'
                                     , n''
                                     , b
                                     )
      where
        (l', n' ,b) = count' n l False
        (r', n'',_) = count' n' r True

-- attr Term
--  inh matchNo :: Int
--  inh recFunName :: String
--  inh isRight :: Bool
--  chn count :: Int
--  syn bcTerm :: Term
--  syn recFunInLeftSubTree :: Bool

test = putStrLn $
       pp testTerm ++ " ~~~> " ++ pp (count "f" testTerm) ++ "\n" ++
       pp testTerm' ++ " ~~~> " ++ pp (count "f" testTerm')
