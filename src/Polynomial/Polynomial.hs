{-# LANGUAGE UndecidableInstances, DataKinds, DeriveAnyClass #-}

module Polynomial.Polynomial 
    ( Polynomial
    , simplify
    , evaluate
    , differentiate
    , coercemonic
    , roots
    , degree
    , leadingCoeff
    , leadingTerm
    , monomial
    , coeff
    ) where

import Polynomial.Ring

import qualified Data.Ratio as R
import qualified GHC.List as L

type Degree = Integer

data Polynomial r
            = Monomial r Degree 
            | Sum (Polynomial r) (Polynomial r)  
            | Product (Polynomial r) (Polynomial r) 
            deriving Eq

instance Num r => Num (Polynomial r) where
    (+) = Sum
    (*) = Product
    abs = id
    signum _ = Monomial 1 0
    negate = (*) (Monomial (-1) 0)
    fromInteger i = Monomial (fromInteger i) 0

instance Functor Polynomial where
    fmap f (Monomial r d) = Monomial (f r) d
    fmap f (Sum a b) = Sum (fmap f a) (fmap f b)
    fmap f (Product a b) = Product (fmap f a) (fmap f b)

instance Foldable Polynomial where
    foldMap f (Monomial r _)  = f r
    foldMap f (Sum p1 p2)     = foldMap f p1 `mappend` foldMap f p2
    foldMap f (Product p1 p2) = foldMap f p1 `mappend` foldMap f p2

instance Ring r => Ring (Polynomial r) where
    (%) a = simplify . snd . divide a
    (//) a = simplify . fst . divide a
    gcd_ = gcdPoly
    div_ = divide
    isUnit p = (degree p == 0) && (isUnit $ leadingCoeff p)
    isZero p = foldr (\t r -> isZero t && r) True $ simplify p

showCoeff :: Rational -> Bool -> String
showCoeff c b
    | c == 1 && b = ""
    | c == (-1) && b = "-"
    | R.denominator c == 1 = show (R.numerator c)
    | R.numerator c == 0 = "0"
    | otherwise = show (R.numerator c) ++ "/" ++ show (R.denominator c)

instance (Show r) => Show (Polynomial r) where
    show :: Polynomial r -> String
    show (Monomial c d)
        | d == 1 = show c ++ "x"
        | d == 0 = show c
        | otherwise = show c ++ "x^" ++ show d
    show (Product a b) = "(" ++ show a ++ ") * (" ++ show b ++ ")"
    show (Sum a b) = show a ++ " + " ++ show b

instance {-# OVERLAPS #-} Show (Polynomial Rational) where
    show :: Polynomial Rational -> String
    show (Monomial c d)
        | d == 1 = showCoeff c True ++ "x"
        | d == 0 = showCoeff c False
        | otherwise = showCoeff c True ++ "x^" ++ show d
    show (Product a b) = "(" ++ show a ++ ") * (" ++ show b ++ ")"
    show (Sum a b) = show a ++ " + " ++ show b
    -- show (Gcd a b) = "GCD(" ++ show a ++ ", " ++ show b ++ ")"
    -- show (Differentiate a) = "(d/dx)[" ++ show a ++ "]"


degree :: Ring r => Polynomial r -> Degree
degree = degree_ . simplify
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
    | otherwise = simplify $ leadingTerm a + leadingTerm b
leadingTerm a = leadingTerm $ simplify a


leadingCoeff :: Ring r => Polynomial r -> r
leadingCoeff = leadingCoeff_ . simplify
    where
        leadingCoeff_ :: Ring r => Polynomial r -> r
        leadingCoeff_ (Monomial c _) = c 
        leadingCoeff_ (Product a b) = leadingCoeff_ a * leadingCoeff_ b
        leadingCoeff_ (Sum a b) | degree a > degree b = leadingCoeff_ a
                                | otherwise = leadingCoeff_ b

divide :: Ring r => Polynomial r -> Polynomial r -> (Polynomial r, Polynomial r)
divide (Monomial c d) (Monomial c' d') 
    | d >= d' = (Monomial (c // c') (d - d'), Monomial (c % c') (d - d'))
    | otherwise = (0, (Monomial c d))
divide a b | degree a < degree b = (0, a)
           | otherwise = let q = Monomial (leadingCoeff a // leadingCoeff b) (degree a - degree b)
                             r = simplify $ a - (q * b)
                         in if isZero q 
                            then (0, r)
                            else case divide r (simplify b) of
                             (q', r') -> (q + q', r')


-- gcd
gcdPoly :: Ring r => Polynomial r -> Polynomial r -> Polynomial r
gcdPoly f g
    | isZero (simplify g) = f
    | isZero (f // ng) = 1
    | otherwise = gcdPoly ng (f % ng)
    where
        ng = fmap (\x_ -> x_ // gcdAll (simplify g)) (simplify g)
        gcdAll :: Ring r => Polynomial r -> r
        gcdAll (Monomial c _) = c
        gcdAll (Sum a b) = gcd_ (gcdAll a) (gcdAll b)
        gcdAll a = gcdAll $ expand a         


-- differentiate
differentiate :: Ring r => Polynomial r -> Polynomial r
differentiate (Monomial a b)
    | b == 0 = Monomial 0 0
    | b > 0 = Monomial (fromIntegral b * a) (b - 1)
differentiate (Sum a b) = (differentiate a) + (differentiate b)
differentiate (Product a b) = ((differentiate a) * b) + (a * (differentiate b)) -- product rule
differentiate a = differentiate $ expand a -- what

-- eliminate multiplication, GCD, Differentiate
expand :: Ring r => Polynomial r -> Polynomial r
expand (Monomial  c d) = Monomial c d
expand (Sum f g) = Sum (expand f) (expand g)
expand (Product (Monomial c0 d0) (Monomial c1 d1)) = Monomial (c0 * c1) (d0 + d1)
expand (Product (Sum f g) h) = Sum (expand $ Product f h) (expand $ Product g h)  -- right dist
expand (Product f (Sum g h)) = Sum (expand $ Product f g) (expand $ Product f h)  -- left dist
expand (Product f g) = expand $ Product (expand f) (expand g)

-- reduce to only Sum and Monomial constructors
setThemUp :: Ring r => Polynomial r -> Polynomial r
setThemUp (Monomial c d) = Monomial c d
setThemUp (Sum (Monomial c d) b) = Sum (Monomial c d) (setThemUp b)
setThemUp (Sum (Sum a b) c) = setThemUp $ Sum a (Sum b c)
setThemUp a = setThemUp $ expand a

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
simplify :: Ring r => Polynomial r -> Polynomial r
simplify = knockThemDown . sortThemOut . setThemUp


coeff :: Ring r => Degree -> Polynomial r -> r
coeff i_ p = coeff_ i_ (simplify p)
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

data C = C 
instance Show C where
    show C = "c"

roots2 :: Ring r => Polynomial r -> [r]
roots2 = roots2_ . simplify
    where
        roots2_ :: Ring r => Polynomial r -> [r]
        roots2_ (Sum (Monomial 1 1) (Monomial a 0)) = [ -a ]
        roots2_ a = error $ "\"" ++ show (fmap (\_ -> C) a) ++ "\" could have multiple roots"
        -- roots2_ (Sum (Monomial 1 2) (Sum (Monomial b 1) (Monomial c 0))) = [(-b + (sqrt (b^2 - 4 * c))) // 2, (-b - (sqrt (b^2 - 4 * c))) // 2]

roots :: (Ring r, Factorable (Polynomial r)) => Polynomial r -> [r]
roots = L.concat . fmap roots2 . factor
        


monomial :: r -> Degree -> Polynomial r
monomial = Monomial