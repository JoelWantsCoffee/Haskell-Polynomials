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
    , monomial
    , coeff
    ) where

import Polynomial.Ring
import qualified Data.Ratio as R

type Degree = Integer

data Polynomial r
            = Monomial r Degree 
            | Sum (Polynomial r) (Polynomial r)  
            | Product (Polynomial r) (Polynomial r)

instance Ring r => Ord (Polynomial r) where
    compare p1 p2 = compare (degree p1) (degree p2)

instance Ring (Polynomial r) => Eq (Polynomial r) where
    (==) x y = isZero (x - y)

instance Num r => Num (Polynomial r) where
    (+) = Sum
    (*) = Product
    abs = id
    signum _ = Monomial 1 0
    negate = (*) (Monomial (-1) 0)
    fromInteger i = Monomial (Prelude.fromInteger i) 0

instance Functor Polynomial where
    fmap f (Monomial r d) = Monomial (f r) d
    fmap f (Sum a b) = Sum (fmap f a) (fmap f b)
    fmap f (Product a b) = Product (fmap f a) (fmap f b)

instance Ring r => Ring (Polynomial r) where
    (%) a = expand . snd . divide a
    (//) a = expand . fst . divide a
    div_ = divide
    isUnit p = (degree p == 0) && (isUnit $ leadingCoeff p)
    isZero p = isZero_ $ expand p
        where
            isZero_ (Sum a b) = (isZero_ a) && (isZero_ b)
            isZero_ (Monomial a _) = isZero a
            isZero_ (Product a b) = (isZero_ a) || (isZero_ b)

instance GCDD r => GCDD (Polynomial r) where
    gcd_ = gcdPoly

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

instance {-# OVERLAPS #-} Show (Polynomial Rational) where
    show :: Polynomial Rational -> String
    show (Monomial c d)
        | d == 1 = showCoeff True ++ "x"
        | d == 0 = showCoeff False
        | otherwise = showCoeff True ++ "x^" ++ show d
        where
            showCoeff :: Bool -> String
            showCoeff b
                | c == 1 && b = ""
                | c == (-1) && b = "-"
                | R.denominator c == 1 = show (R.numerator c)
                | R.numerator c == 0 = "0"
                | otherwise = show (R.numerator c) ++ "/" ++ show (R.denominator c)
    show (Product a b) = "(" ++ show a ++ ") * (" ++ show b ++ ")"
    show (Sum a b) = show a ++ " + " ++ show b


degree :: Ring r => Polynomial r -> Degree
degree = degree_ . expand
    where
        degree_ :: Ring r => Polynomial r -> Degree
        degree_ (Monomial 0 _) = 0
        degree_ (Monomial _ deg) = deg
        degree_ (Sum p1 p2) = max (degree p1) (degree p2)
        degree_ (Product p1 p2) = degree p1 + degree p2


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


fromList :: Ring r => [(r, Degree)] -> Polynomial r
fromList [] = monomial 0 0
fromList lst = foldr1 (*) $ (uncurry monomial) <$> lst

toList :: Ring r => Polynomial r -> [(r, Degree)]
toList = toList_ . expand
    where
        toList_ (Sum a b) = (toList_ a) ++ (toList_ b)
        toList_ (Monomial c d) = [(c,d)]


divide :: Ring r => Polynomial r -> Polynomial r -> (Polynomial r, Polynomial r)
divide (Monomial c d) (Monomial c' d') 
    | d >= d' = (Monomial (c // c') (d - d'), Monomial (c % c') (d - d'))
    | otherwise = (0, (Monomial c d))
divide a b | degree a < degree b = (0, a)
           | otherwise = let q = Monomial (leadingCoeff a // leadingCoeff b) (degree a - degree b)
                             r = expand $ a - (q * b)
                         in if isZero q 
                            then (0, r)
                            else case divide r (expand b) of
                             (q', r') -> (q + q', r')


-- gcd
gcdPoly :: GCDD r => Polynomial r -> Polynomial r -> Polynomial r
gcdPoly f g
    | isZero (expand g) = f
    | isZero (f // ng) = 1
    | otherwise = gcdPoly ng (f % ng)
    where
        ng = fmap (\x_ -> x_ // gcdAll (expand g)) (expand g)
        gcdAll :: GCDD r => Polynomial r -> r
        gcdAll (Monomial c _) = c
        gcdAll (Sum a b) = gcd_ (gcdAll a) (gcdAll b)
        gcdAll a = gcdAll $ ungroup a         


-- differentiate
differentiate :: Ring r => Polynomial r -> Polynomial r
differentiate (Monomial a b)
    | b == 0 = Monomial 0 0
    | b > 0 = Monomial (fromIntegral b * a) (b - 1)
differentiate (Sum a b) = (differentiate a) + (differentiate b)
differentiate (Product a b) = ((differentiate a) * b) + (a * (differentiate b)) -- product rule
differentiate a = differentiate $ ungroup a -- what

-- eliminate multiplication, GCD, Differentiate
ungroup :: Ring r => Polynomial r -> Polynomial r
ungroup (Monomial  c d) = Monomial c d
ungroup (Sum f g) = Sum (ungroup f) (ungroup g)
ungroup (Product (Monomial c0 d0) (Monomial c1 d1)) = Monomial (c0 * c1) (d0 + d1)
ungroup (Product (Sum f g) h) = Sum (ungroup $ Product f h) (ungroup $ Product g h)  -- right dist
ungroup (Product f (Sum g h)) = Sum (ungroup $ Product f g) (ungroup $ Product f h)  -- left dist
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


coeff :: Ring r => Degree -> Polynomial r -> r
coeff i_ p = coeff_ i_ (expand p)
    where
        coeff_ :: Ring r => Degree -> Polynomial r -> r
        coeff_ i (Sum (Monomial c d) b) = if d == i then c else coeff_ i b
        coeff_ i (Sum b (Monomial c d)) = if d == i then c else coeff_ i b
        coeff_ i (Monomial c d) = if d == i then c else 0
        coeff_ _ _ = error "Polynomial must be simplified." 


evaluate :: Ring r => r -> Polynomial r -> r
evaluate r (Monomial c d) = c * (r ^ d)
evaluate r (Sum a b) = (evaluate r a) + (evaluate r b)
evaluate r (Product a b) = (evaluate r a) * (evaluate r b)

coercemonic :: Ring r => Polynomial r -> (r, Polynomial r)
coercemonic p = if isUnit lc then (lc, (monomial lcinv 0) * p) else (1, p)
    where
        lcinv = (1 // lc)
        lc = leadingCoeff p

monomial :: r -> Degree -> Polynomial r
monomial = Monomial