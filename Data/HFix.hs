{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

module Data.HFix where

import Control.Applicative (Applicative, liftA2)
import Control.Monad (Monad, (<=<))

data HFix (f :: (a -> *) -> (a -> *)) (k :: a) = HFix { unHFix :: f (HFix f) k }

class HFunctor (f :: (a -> *) -> (a -> *)) where
    hmap :: (∀ k . s k -> t k) -> f s k -> f t k

class HTraversable (f :: (a -> *) -> (a -> *)) where
    htraverse :: Applicative p => (∀ k . s k -> p (t k)) -> f s k -> p (f t k)

data I k' φ k = I (φ k')
data K a φ k = K a
data (f :+: g) φ k = L (f φ k) | R (g φ k)
data (f :×: g) φ k = f φ k :×: g φ k
data (f :▻: k') φ k where
    Tag :: f φ k' -> (f :▻: k') φ k'

instance HFunctor (I k') where
    hmap f (I x) = I (f x)

instance HTraversable (I k') where
    htraverse f (I x) = I <$> f x

instance HFunctor (K a) where
    hmap _ (K a) = K a

instance HTraversable (K a) where
    htraverse _ (K a) = pure (K a)

instance (HFunctor f, HFunctor g) => HFunctor (f :+: g) where
    hmap f (L x) = L (hmap f x)
    hmap f (R y) = R (hmap f y)

instance (HTraversable f, HTraversable g) => HTraversable (f :+: g) where
    htraverse f (L x) = L <$> htraverse f x
    htraverse f (R y) = R <$> htraverse f y

instance (HFunctor f, HFunctor g) => HFunctor (f :×: g) where
    hmap f (x :×: y) = hmap f x :×: hmap f y

instance (HTraversable f, HTraversable g) => HTraversable (f :×: g) where
    htraverse f (x :×: y) = liftA2 (:×:) (htraverse f x) (htraverse f y)

instance HFunctor f => HFunctor (f :▻: k') where
    hmap f (Tag x) = Tag (hmap f x)

instance HTraversable f => HTraversable (f :▻: k') where
    htraverse f (Tag x) = Tag <$> htraverse f x

class f :≤: g where
    inj :: f φ k -> g φ k
    proj :: g φ k -> Maybe (f φ k)

instance f :≤: f where
    inj = id
    proj = Just

instance f :≤: (f :+: g) where
    inj = L
    proj (L x) = Just x
    proj (R _) = Nothing

instance f :≤: g => f :≤: (h :+: g) where
    inj = R . inj
    proj (L _) = Nothing
    proj (R y) = proj y

type Alg f φ k = (f φ k) -> φ k

cata :: HFunctor f => (∀ k . Alg f φ k) -> HFix f k -> φ k
cata alg = alg . hmap (cata alg) . unHFix

type AlgM m f φ k = (f φ k) -> m (φ k)

cataM :: (HTraversable f, Monad m) => (∀ k . AlgM m f φ k) -> HFix f k -> m (φ k)
cataM algM = algM <=< htraverse (cataM algM) . unHFix
