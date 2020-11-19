{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Servant.Validate.Internal (
    ApiTree(..)
  , Compare, Cases, MergeSortedUnique, MergePaths, MergeTree
  , compSym, sMergeSortedUnique, sMergePaths, sMergeTree
  , SApiTree(..) , toSApiTree
  , Prod(..), Tup(..), SSym(..)
  , toProd, reflectProd, toTup, reflectTup, toSSym, reflectSSym
  ) where

import           Data.Kind
import           Unsafe.Coerce
import           Data.Proxy
import           Data.Text       (Text)
import           GHC.TypeLits
import           Type.Reflection
import qualified Data.Text       as T

data ApiTree = Branch [Symbol] [(Symbol, ApiTree)]

type family Compare (a :: k) (b :: k) :: Ordering
type instance Compare (a :: Symbol) (b :: Symbol) = CmpSymbol a b

type family Cases (c :: Ordering) (lt :: k) (eq :: k) (gt :: k) where
    Cases 'LT lt eq gt = lt
    Cases 'EQ lt eq gt = eq
    Cases 'GT lt eq gt = gt

type family MergeSortedUnique err (xs :: [k]) (ys :: [k]) :: [k] where
    MergeSortedUnique err '[]       '[]       = '[]
    MergeSortedUnique err '[]       (y ': ys) = y ': ys
    MergeSortedUnique err (x ': xs) '[]       = x ': xs
    MergeSortedUnique err (x ': xs) (y ': ys) = Cases
      (Compare x y)
      (x ': MergeSortedUnique err xs (y ': ys))
      (TypeError (err ':<>: 'Text ": " ':<>: ShowType x))
      (y ': MergeSortedUnique err (x ': xs) ys)

type family MergePaths (base :: [Symbol]) (xs :: [(Symbol, ApiTree)]) (ys :: [(Symbol, ApiTree)]) :: [(Symbol, ApiTree)] where
    MergePaths base '[]                '[]                = '[]
    MergePaths base '[]                ( '(b, y) ': bys ) = '(b, y) ': bys
    MergePaths base ( '(a, x) ': axs ) '[]                = '(a, x) ': axs
    MergePaths base ( '(a, x) ': axs ) ( '(b, y) ': bys ) = Cases
      (Compare a b)
      ( '(a, x) ': MergePaths base axs ( '(b, y) ': bys ) )
      ( '(a, MergeTree (a ': base) x y) ': MergePaths base axs bys )
      ( '(b, y) ': MergePaths base ( '(a, x) ': axs ) bys )

type family MergeTree (base :: [Symbol]) (a :: ApiTree) (b :: ApiTree) :: ApiTree where
    MergeTree base ('Branch mA pA) ('Branch mB pB) =
        'Branch
            (MergeSortedUnique
                ('Text "Duplicate method in API at path " ':<>: 'Text ("/" `AppendSymbol` ShowPath base))
                mA mB
            )
            (MergePaths base pA pB)

type family ShowPath (path :: [Symbol]) :: Symbol where
    ShowPath '[] = ""
    ShowPath '[x] = x
    ShowPath (x ': y ': xs) = x `AppendSymbol` "/" `AppendSymbol` ShowPath (y ': xs)





-- a bunch of stuff to avoid needing a singletons dep.  this isn't needed
-- for any of the compile-stuff, it's just useful for reflection to
-- a value-level map


data Prod :: (k -> Type) -> [k] -> Type where
    PNil :: Prod f '[]
    (:<) :: f a -> Prod f as -> Prod f (a ': as)
infixr 5 :<
deriving instance (forall a. Show (f a)) => Show (Prod f as)

toProd :: forall k (as :: [k]) f. (forall (a :: k). TypeRep a -> f a) -> TypeRep as -> Prod f as
toProd f = go
  where
    go :: forall (bs :: [k]). TypeRep bs -> Prod f bs
    go = \case
      Con _            -> unsafeCoerce PNil
      App (App _ x) xs -> unsafeCoerce $ f (unsafeCoerce x) :< go (unsafeCoerce xs)

reflectProd :: forall k (as :: [k]) f r. (forall (a :: k). f a -> r) -> Prod f as -> [r]
reflectProd f = go
  where
    go :: forall (bs :: [k]). Prod f bs -> [r]
    go = \case
      PNil    -> []
      x :< xs -> f x : go xs

data Tup :: (a -> Type) -> (b -> Type) -> (a, b) -> Type where
    Tup :: f x -> g y -> Tup f g '(x, y)
deriving instance (forall a. Show (f a), forall a. Show (g a)) => Show (Tup f g xy)

toTup :: (forall x. TypeRep x -> f x) -> (forall x. TypeRep x -> g x) -> TypeRep xy -> Tup f g xy
toTup f g (App (App _ x) y) = unsafeCoerce $ Tup (f (unsafeCoerce x)) (g (unsafeCoerce y))

reflectTup :: forall j k (xy :: (j, k)) f g a b. (forall (x :: j). f x -> a) -> (forall (y :: k). g y -> b) -> Tup f g xy -> (a, b)
reflectTup f g (Tup x y) = (f x, g y)

data SSym :: Symbol -> Type where
    SSym :: KnownSymbol s => SSym s
deriving instance Show (SSym s)
toSSym :: TypeRep s -> SSym s
toSSym tr = case someSymbolVal (read (show tr) :: String) of
  SomeSymbol (Proxy :: Proxy b) -> unsafeCoerce (SSym :: SSym b)
reflectSSym :: forall s. SSym s -> Text
reflectSSym s@SSym = T.pack $ symbolVal s

data SApiTree :: ApiTree -> Type where
    SBranch :: Prod SSym ms -> Prod (Tup SSym SApiTree) ts -> SApiTree ('Branch ms ts)
deriving instance Show (SApiTree api)
toSApiTree :: TypeRep api -> SApiTree api
toSApiTree (App (App _ ms) ts) = unsafeCoerce $
    SBranch (toProd toSSym (unsafeCoerce ms))
            (toProd (toTup toSSym toSApiTree) (unsafeCoerce ts))

data SOrdering :: Ordering -> Type where
    SLT :: SOrdering 'LT
    SEQ :: SOrdering 'EQ
    SGT :: SOrdering 'GT

compSym
    :: forall a b. ()
    => SSym a
    -> SSym b
    -> SOrdering (CmpSymbol a b)
compSym a@SSym b@SSym = case compare (symbolVal a) (symbolVal b) of
    LT -> unsafeCoerce SLT
    EQ -> unsafeCoerce SEQ
    GT -> unsafeCoerce SGT

sMergeSortedUnique
    :: forall err xs ys. ()
    => Prod SSym xs
    -> Prod SSym ys
    -> Prod SSym (MergeSortedUnique err xs ys)
sMergeSortedUnique = \case
    PNil -> \case
      PNil    -> PNil
      y :< ys -> y :< ys
    x :< xs -> \case
      PNil    -> x :< xs
      y :< ys -> case compSym x y of
        SLT -> x :< sMergeSortedUnique @err xs (y :< ys)
        SEQ -> error "sMergeSortedUnique: forbidden by type system"
        SGT -> y :< sMergeSortedUnique @err (x :< xs) ys

sMergePaths
    :: forall base xs ys. ()
    => Prod (Tup SSym SApiTree) xs
    -> Prod (Tup SSym SApiTree) ys
    -> Prod (Tup SSym SApiTree) (MergePaths base xs ys)
sMergePaths = \case
    PNil -> \case
      PNil -> PNil
      Tup b y :< bys -> Tup b y :< bys
    Tup (a :: SSym a) x :< axs -> \case
      PNil -> Tup a x :< axs
      Tup b y :< bys -> case compSym a b of
        SLT -> Tup a x :< sMergePaths @base axs (Tup b y :< bys)
        SEQ -> Tup a (sMergeTree @(a ': base) x y) :< sMergePaths @base axs bys
        SGT -> Tup b y :< sMergePaths @base (Tup a x :< axs) bys

sMergeTree :: forall base a b. SApiTree a -> SApiTree b -> SApiTree (MergeTree base a b)
sMergeTree (SBranch mA pA) (SBranch mB pB) = SBranch undefined (sMergePaths @base pA pB)
