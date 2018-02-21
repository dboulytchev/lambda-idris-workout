module TSyntax 

%default total

infixl 7 :@
prefix 8 :?
prefix 9 :!
prefix 8 :\

data GTerm : Nat -> Type where 
  (:\) : GTerm (n+1)            -> GTerm n 
  (:@) : GTerm n     -> GTerm n -> GTerm n 
  (:?) : String                 -> GTerm n
  (:!) : (i:Nat)     -> LTE i n -> GTerm n 

Term : Type
Term = GTerm 0

z : Term
z = (:?) "Z"

id : Term
id = (:\) ((:!) 0 LTEZero)

id2 : Term
id2 = (:\) ((:!) 1 lteRefl)

-- implementation Eq Term where
--   (:\ a)   == (:\ b)   = a == b
--   (:? x)   == (:? y)   = x == y
--   (:! x)   == (:! y)   = x == y
--   (a :@ b) == (c :@ d) = a == c && b == d
--   _        == _        = False
  
-- app : Term
-- app = :\ (:\ :!1 :@ :!0)

-- omega : Term
-- omega = (:\ (:!0 :@ :!0)) :@ (:\ (:!0 :@ :!0))

-- y : Term
-- y = :\ ((:\ (:!1 :@ (:!0 :@ :!0))) :@ (:\ (:!1 :@ (:!0 :@ :!0))))

-- z : Term
-- z = :\ id

-- one : Term
-- one = app

-- two : Term
-- two = :\ (:\ (:!1 :@ (:!1 :@ :!0)))

-- three : Term
-- three = :\ (:\ :!1 :@ (:!1 :@ (:!1 :@ :!0)))

-- plusReducesS : (n:Nat) -> n < S n = True
-- plusReducesS Z = Refl
-- plusReducesS (S m) = ?rhs

lift : Nat -> GTerm i -> GTerm (S i)
lift _ s@(:? _)  = s
lift m s@((:!) n e) = if n > m then ((:!) (S n) (LTESucc e)) else ((:!) n (lteSuccRight e))
lift m (a :@ b) = lift m a :@ lift m b
lift m (:\ a)   = :\ lift (m+1) a

-- subst : Term -> Nat -> Term -> Term
-- subst s@(:? _) _ _ = s
-- subst s@(:! n) m x = if n == m then x else s 
-- subst s@(:\ n) m x = :\ (subst n (m+1) $ lift 0 x)
-- subst (a :@ b) n x = subst a n x :@ subst b n x

-- eval0 : Term -> Term
-- eval0   ((:\ a) :@ b) = subst a 1 b
-- eval0 s@(:? _)        = s
-- eval0 s@(:! _)        = s
-- eval0   (:\ a)        = :\ (eval0 a)
-- eval0   (a :@ b)      = if a == a' then a :@ (eval0 b) else a' :@ b where
--   a' = eval0 a
  
-- partial 
-- no : Term -> Term
-- no a = if a' == a then a' else no a' where
--   a' = eval0 a

{-
 let add   = "m" => ("n" => ("f" => ("x" => (!"m" @ !"f") @ ((!"n" @ !"f") @ !"x"))))
 let mul   = "m" => ("n" => ("f" => ("x" => (!"m" @ (!"n" @ !"f")) @ !"x")))
-}

