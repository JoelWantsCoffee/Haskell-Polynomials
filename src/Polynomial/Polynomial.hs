{-# LANGUAGE UndecidableInstances, DataKinds, DeriveAnyClass #-}

module Polynomial.Polynomial 
    ( Polynomial
    , expand
    , evaluate
    , differentiate
    , coercemonic
    , degree
    , toList
    , fromList
    , leadingCoeff
    , leadingTerm
    , polyDivMod
    , monomial
    , primitivePart
    , coeff
    ) where

import Polynomial.Ring
import qualified Data.Ratio as R

type Degree = Integer

data Polynomial r
            = Monomial r Degree
            | Sum (Polynomial r) (Polynomial r)
            | Product (Polynomial r) (Polynomial r)


instance Functor Polynomial where
    fmap f (Monomial r d) = Monomial (f r) d
    fmap f (Sum a b) = Sum (fmap f a) (fmap f b)
    fmap f (Product a b) = Product (fmap f a) (fmap f b)


instance (Show r, Ring r) => Show (Polynomial r) where
    show :: Polynomial r -> String
    show (Monomial c d)
        | d == 1 = showCoeff True ++ "x"
        | d == 0 = showCoeff False
        | otherwise = showCoeff True ++ "x^" ++ show d
        where
            showCoeff :: Bool -> String
            showCoeff b
                | c == 1 && b = ""
                | c == (-1) && b = "-"
                | otherwise = show c
    show (Product a b) = "(" ++ show a ++ ") * (" ++ show b ++ ")"
    show (Sum a b) = show a ++ " + " ++ show b


-- instance {-# OVERLAPS #-} Show (Polynomial Rational) where
--     show :: Polynomial Rational -> String
--     show (Monomial c d)
--         | d == 1 = showCoeff True ++ "x"
--         | d == 0 = showCoeff False
--         | otherwise = showCoeff True ++ "x^" ++ show d
--         where
--             showCoeff :: Bool -> String
--             showCoeff b
--                 | c == 1 && b = ""
--                 | c == (-1) && b = "-"
--                 | R.denominator c == 1 = show (R.numerator c)
--                 | R.numerator c == 0 = "0"
--                 | otherwise = show (R.numerator c) ++ "/" ++ show (R.denominator c)
--     show (Product a b) = "(" ++ show a ++ ") * (" ++ show b ++ ")"
--     show (Sum a b) = show a ++ " + " ++ show b


instance Num r => Num (Polynomial r) where
    (+) = Sum
    (*) = Product
    abs = id
    signum _ = Monomial 1 0
    negate = (*) (Monomial (-1) 0)
    fromInteger i = Monomial (fromInteger i) 0


instance (Ord r, Ring r) => Ord (Polynomial r) where
    compare p1 p2 = if (degree p1) == (degree p2)
        then compare (toList p1) (toList p2)
        else compare (degree p1) (degree p2)


instance Ring r => Eq (Polynomial r) where
    (==) x y = isZero (x - y)
        where
            isZero p = isZero_ $ expand p
            
            isZero_ (Sum a b) = (isZero_ a) && (isZero_ b)
            isZero_ (Monomial a _) = a == 0
            isZero_ (Product a b) = (isZero_ a) || (isZero_ b)


instance Ring r => Ring (Polynomial r) where
    (/.) a = expand . divide a
    isUnit p = (degree p == 0) && (isUnit $ leadingCoeff p)


instance ED r => GCDD (Polynomial r) where
    gcd_ :: ED r => Polynomial r -> Polynomial r -> Polynomial r
    gcd_ f g    | f == 0 = g
                | g == 0 = f
                | degree g < 1 = base
                | (not $ isUnit $ leadingCoeff g_) = base
                | otherwise = base * (gcd_ g_ $ snd $ polyDivMod f_ g_)
                where
                    (fc, f_) = primitivePart f   
                    (gc, g_) = primitivePart g
                    base = monomial (gcd_ fc gc) 0


instance Field r => ED (Polynomial r) where
    (//) a = expand . fst . polyDivMod a
    (%) a = expand . snd . polyDivMod a
    div_ = polyDivMod
    euclidean = degree


fromList :: Ring r => [(r, Degree)] -> Polynomial r
fromList [] = monomial 0 0
fromList lst = foldr1 (*) $ (uncurry monomial) <$> lst


toList :: Ring r => Polynomial r -> [(r, Degree)]
toList = toList_ . expand
    where
        toList_ (Sum a b) = (toList_ a) ++ (toList_ b)
        toList_ (Monomial c d) = [(c,d)]
        toList_ _ = undefined


leadingTerm :: Ring r => Polynomial r -> Polynomial r
leadingTerm (Monomial c d) = Monomial c d
leadingTerm (Sum a b)
    | degree a > degree b = leadingTerm a
    | degree a < degree b = leadingTerm b
    | otherwise = expand $ leadingTerm a + leadingTerm b
leadingTerm a = leadingTerm $ expand a


leadingCoeff :: Ring r => Polynomial r -> r
leadingCoeff = leadingCoeff_ . expand
    where
        leadingCoeff_ :: Ring r => Polynomial r -> r
        leadingCoeff_ (Monomial c _) = c 
        leadingCoeff_ (Product a b) = leadingCoeff_ a * leadingCoeff_ b
        leadingCoeff_ (Sum a b) | degree a > degree b = leadingCoeff_ a
                                | otherwise = leadingCoeff_ b


coeff :: Ring r => Degree -> Polynomial r -> r
coeff i_ p = coeff_ i_ (expand p)
    where
        coeff_ :: Ring r => Degree -> Polynomial r -> r
        coeff_ i (Sum (Monomial c d) b) = if d == i then c else coeff_ i b
        coeff_ i (Sum b (Monomial c d)) = if d == i then c else coeff_ i b
        coeff_ i (Monomial c d) = if d == i then c else 0
        coeff_ _ _ = error "Polynomial must be simplified." 

degree :: Ring r => Polynomial r -> Degree
degree = degree_ . expand
    where
        degree_ :: Ring r => Polynomial r -> Degree
        degree_ (Monomial 0 _) = 0
        degree_ (Monomial _ deg) = deg
        degree_ (Sum p1 p2) = max (degree p1) (degree p2)
        degree_ (Product p1 p2) = degree p1 + degree p2


primitivePart :: GCDD r => Polynomial r -> (r, Polynomial r)
primitivePart p = (c, (flip (/.) c) <$> expand p)
    where
        c = foldr1 gcd_ . fmap fst . toList $ p


coercemonic :: Field r => Polynomial r -> (r, Polynomial r)
coercemonic p = if isUnit lc then (lc, (monomial lcinv 0) * p) else (1, p)
    where
        lcinv = (1 // lc)
        lc = leadingCoeff p


evaluate :: Ring r => r -> Polynomial r -> r
evaluate r (Monomial c d) = c * (r ^ d)
evaluate r (Sum a b) = (evaluate r a) + (evaluate r b)
evaluate r (Product a b) = (evaluate r a) * (evaluate r b)


monomial :: r -> Degree -> Polynomial r
monomial = Monomial


-- differentiate
differentiate :: Ring r => Polynomial r -> Polynomial r
differentiate (Monomial a b)
    | b == 0 = Monomial 0 0
    | b > 0 = Monomial (fromIntegral b * a) (b - 1)
differentiate (Sum a b) = (differentiate a) + (differentiate b)
differentiate (Product a b) = ((differentiate a) * b) + (a * (differentiate b)) -- product rule
differentiate a = differentiate $ ungroup a -- what


divide :: Ring r => Polynomial r -> Polynomial r -> Polynomial r
divide (Monomial c d) (Monomial c' d')
    | d >= d' = Monomial (c /. c') (d - d')
    | otherwise = 0
divide a b
    | degree a < degree b = 0
    | q == 0 = 0
    | otherwise = (+) q $ divide r (expand b)
    where
        q = Monomial (leadingCoeff a /. leadingCoeff b) (degree a - degree b)
        r = expand $ a - (q * b)

{-  DEFINITION

    polyDivMod : a -> b -> (q,r)
        returns q,r such that:
        1.  a = b * q + r
        2.  if there exists q' such that a = b * q' then r = 0
        3.  if R is a field then r = 0, or degree( r ) < degree( b )
    
    
    PROOF
        case 1: ax^c -> bx^d -> ( qx^(c-d) , rx^c  ) for (q,r) = ediv(a,b)
            1.  qx^(c-d) * bx^d + rx^c  = bqx^c + rx^c
                                        = (bq + r)x^c
                                        = ax^c
            2.  ax^c = bx^d * q'x^e
                        => e = c - d
                        => a = b * q'
                        => r = 0
                        => rx^c = 0

            3.  R is a field 
                        => a | b
                        => r = 0 
                        => rx^c = 0
        
        case 2: (ax^n + f_a(x)) -> (bx^m + f_b(x)) -> ( (a/b)x^(n-m) + g() , rx^c ) for c >= d and (q,r) = ediv(a,b)
            1.  ( a // b ) * x^(n - m) + ( a - )


            (ax^n + f_a(x)) - ( a // b ) * x^(n - m) * (bx^m + f_b(x))
                = (ax^n + f_a(x)) - (b * (a // b)) * x^n - f_a(x) * (bx^m + f_b(x))
                = (a - (b * (a // b)) ) x^n + f_a(x) - f_a(x) * (bx^m + f_b(x))
                = (a - (b * (a // b)) ) x^n + f_a(x) - f_a(x) * (bx^m + f_b(x))


-}
polyDivMod :: ED r => Polynomial r -> Polynomial r -> (Polynomial r, Polynomial r)
polyDivMod a@(Monomial c d) (Monomial c' d')
    | d < d' = (0, a)
    | otherwise = (Monomial (c // c') (d - d'), Monomial (c % c') d)
polyDivMod a b
    | degree a < degree b = (0, a)
    | q == 0 = (0, r)
    | otherwise = (\(q', r') -> (q + q', r')) $ polyDivMod r (expand b)
    where
        q = Monomial (leadingCoeff a // leadingCoeff b) (degree a - degree b)
        r = expand $ a - (q * b)

-- remove Product
ungroup :: Ring r => Polynomial r -> Polynomial r
ungroup (Monomial  c d) = Monomial c d
ungroup (Sum f g) = Sum (ungroup f) (ungroup g)
ungroup (Product (Monomial c0 d0) (Monomial c1 d1)) = Monomial (c0 * c1) (d0 + d1)
ungroup (Product (Sum f g) h) = Sum (ungroup $ Product f h) (ungroup $ Product g h)
ungroup (Product f (Sum g h)) = Sum (ungroup $ Product f g) (ungroup $ Product f h)
ungroup (Product f g) = ungroup $ Product (ungroup f) (ungroup g)

-- reduce to only Sum and Monomial constructors
setThemUp :: Ring r => Polynomial r -> Polynomial r
setThemUp (Monomial c d) = Monomial c d
setThemUp (Sum (Monomial c d) b) = Sum (Monomial c d) (setThemUp b)
setThemUp (Sum (Sum a b) c) = setThemUp $ Sum a (Sum b c)
setThemUp a = setThemUp $ ungroup a

-- sort Sum and Monomial constructors, returns a only-right-recursive tree
sortThemOut :: Ring r => Polynomial r -> Polynomial r
sortThemOut (Monomial c_ d) = Monomial c_ d
sortThemOut (Sum (Monomial c_ d_) t) = Sum big $ sortThemOut rest
        where 
            (big, rest) = findBig (Monomial c_ d_) t id
            findBig :: Ring r 
                => Polynomial r 
                -> Polynomial r 
                -> (Polynomial r -> Polynomial r) 
                -> (Polynomial r, Polynomial r)
            findBig (Monomial maxc maxd) (Monomial c d) f
                | d > maxd  = (Monomial c d, f $ Monomial maxc maxd)
                | otherwise = (Monomial maxc maxd, f $ Monomial c d)
            findBig (Monomial maxc maxd) (Sum (Monomial c d) next) f
                | d > maxd  = findBig (Monomial c d) next ((.) f $ Sum (Monomial maxc maxd))
                | otherwise = findBig (Monomial maxc maxd) next ((.) f $ Sum (Monomial c d))
            findBig b n f = findBig b (setThemUp n) f
sortThemOut a = sortThemOut $ setThemUp a

-- remove duplicate power monomials
knockThemDown :: Ring r => Polynomial r -> Polynomial r
knockThemDown (Monomial c d) = Monomial c d
knockThemDown (Sum (Monomial 0 _) a) = knockThemDown a
knockThemDown (Sum a (Monomial 0 _)) = knockThemDown a
knockThemDown (Sum (Monomial c d) (Sum (Monomial c' d') t))
    | d == d' = knockThemDown $ Sum (Monomial (c + c') d) t
    | otherwise = Sum (Monomial c d) $ knockThemDown (Sum (Monomial c' d') t)
knockThemDown (Sum (Monomial c d) (Monomial c' d'))
    | d == d' = Monomial (c + c') d
    | otherwise = Sum (Monomial c d) (Monomial c' d')
knockThemDown a = knockThemDown $ sortThemOut a

-- convert to an only-right-recursive tree where each monomial degree appears at most once 
expand :: Ring r => Polynomial r -> Polynomial r
expand = knockThemDown . sortThemOut . setThemUp