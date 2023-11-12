-- {-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE EmptyDataDecls #-}
-- {-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE FunctionalDependencies #-}
-- {-# LANGUAGE KindSignatures #-}
-- {-# LANGUAGE MultiParamTypeClasses #-}
-- {-# LANGUAGE PatternGuards #-}
-- {-# LANGUAGE Rank2Types #-}
-- {-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
-- {-# LANGUAGE PolyKinds #-}
-- {-# LANGUAGE TypeOperators #-}
-- {-# LANGUAGE TemplateHaskell #-}
-- {-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE DeriveDataTypeable #-}
-- {-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
-- {-# OPTIONS_GHC -fno-cse #-}
-- {-# OPTIONS_GHC -fno-full-laziness #-}
-- {-# OPTIONS_GHC -fno-float-in #-}
-- {-# OPTIONS_GHC -fno-warn-orphans #-}
-- {-# OPTIONS_GHC -fno-warn-unused-binds #-}


import GHC.Types
import GHC.Magic.Dict
import Unsafe.Coerce

data Nat = Zero | Succ Nat

class KnownNat (n :: Nat) where 
    natVal :: Proxy n -> Integer

instance KnownNat Zero where 
    natVal _ = 0

instance KnownNat (n :: Nat) => KnownNat (Succ n) where
    natVal _ = 1 + (natVal (Proxy :: Proxy n))  

showNat :: forall n. KnownNat (n :: Nat) => Proxy n -> String
showNat _ = show (natVal @n)

data Proxy a = Proxy
newtype Trick r = Trick (forall (n :: Nat). KnownNat n => Proxy n -> r)
reifyNat :: forall r. Integer -> (forall (n :: Nat). KnownNat n => Proxy n -> r) -> r
reifyNat i k = unsafeCoerce (Trick k :: Trick r) (\_ -> i) Proxy


withKnownNat :: forall n rep (r :: TYPE rep).
                Proxy n -> (KnownNat n => r) -> r
withKnownNat = withDict @(KnownNat n)