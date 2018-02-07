module Syntax 

%default total

infixl 7 :@
prefix 8 :?
prefix 9 :!
prefix 8 :\

data Term = 
  (:\) Term 
| (:@) Term Term 
| (:?) String 
| (:!) Nat 

implementation Show Term where
  show (:\ a)   = "/ " ++ show a
  show (:? x)   = x
  show (:! n)   = show n
  show (a :@ b) = abr (show a) ++ " @ " ++ bbr (show b) where
    abr = case a of
            (:\ _) => (\s => "(" ++ s ++ ")")
            _      => (\s => s)
    bbr = case b of
            (_ :@ _) => (\s => "(" ++ s ++ ")")
            _        => (\s => s)
       
  
implementation Eq Term where
  (:\ a)   == (:\ b)   = a == b
  (:? x)   == (:? y)   = x == y
  (:! x)   == (:! y)   = x == y
  (a :@ b) == (c :@ d) = a == c && b == d
  _        == _        = False
  
id : Term
id = :\ :!0

app : Term
app = :\ (:\ :!1 :@ :!0)

omega : Term
omega = (:\ (:!0 :@ :!0)) :@ (:\ (:!0 :@ :!0))

y : Term
y = :\ ((:\ (:!1 :@ (:!0 :@ :!0))) :@ (:\ (:!1 :@ (:!0 :@ :!0))))

z : Term
z = :\ id

one : Term
one = app

two : Term
two = :\ (:\ (:!1 :@ (:!1 :@ :!0)))

three : Term
three = :\ (:\ :!1 :@ (:!1 :@ (:!1 :@ :!0)))

lift : Nat -> Term -> Term
lift _ s@(:?_)  = s
lift m s@(:! n) = if n > m then :! (n+1) else s                
lift m (a :@ b) = lift m a :@ lift m b
lift m (:\ a)   = :\ lift (m+1) a 

subst : Term -> Nat -> Term -> Term
subst s@(:? _) _ _ = s
subst s@(:! n) m x = if n == m then x else s 
subst s@(:\ n) m x = :\ (subst n (m+1) $ lift 0 x)
subst (a :@ b) n x = subst a n x :@ subst b n x

eval0 : Term -> Term
eval0   ((:\ a) :@ b) = subst a 0 b
eval0 s@(:? _)        = s
eval0 s@(:! _)        = s
eval0   (:\ a)        = :\ (eval0 a)
eval0   (a :@ b)      = if a == a' then a :@ (eval0 b) else a' :@ b where
  a' = eval0 a
  
partial 
no : Term -> Term
no a = if a' == a then a' else no a' where
  a' = eval0 a

{-
 let add   = "m" => ("n" => ("f" => ("x" => (!"m" @ !"f") @ ((!"n" @ !"f") @ !"x"))))
 let mul   = "m" => ("n" => ("f" => ("x" => (!"m" @ (!"n" @ !"f")) @ !"x")))
-}

