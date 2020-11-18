{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Servant.Validate where

import           Data.Kind
import           Data.Map           (Map)
import           Data.Proxy
import           Data.Set           (Set)
import           Data.Text          (Text)
import           Data.Type.Bool
import           Data.Type.Equality
import           GHC.TypeLits
import           Servant.API
import           Type.Reflection
import           Unsafe.Coerce
import qualified Data.Map           as M
import qualified Data.Set           as S
import qualified Data.Text          as T

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
      ( '(a, MergeTree base x y) ': MergePaths base axs bys )
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
    ShowPath (x ': xs) = x `AppendSymbol` "/" `AppendSymbol` ShowPath xs


class HasApiTree (base :: [Symbol]) (api :: Type) where
    type ToApiTree base api :: ApiTree

instance HasApiTree (path ': base) api => HasApiTree base ((path :: Symbol) :> api) where
    type ToApiTree base (path :> api) = 'Branch '[] '[ '(path, ToApiTree (path ': base) api) ]

instance (HasApiTree base a, HasApiTree base b) => HasApiTree base (a :<|> b) where
    type ToApiTree base (a :<|> b) = MergeTree base (ToApiTree base a) (ToApiTree base b)

class MethodString k where
    type ToMethodString (x :: k) :: Symbol

instance MethodString StdMethod where
    type ToMethodString 'PATCH = "PATCH"
    type ToMethodString 'OPTIONS = "OPTIONS"
    type ToMethodString 'CONNECT = "CONNECT"
    type ToMethodString 'TRACE = "TRACE"
    type ToMethodString 'DELETE = "DELETE"
    type ToMethodString 'PUT = "PUT"
    type ToMethodString 'HEAD = "HEAD"
    type ToMethodString 'POST = "POST"
    type ToMethodString 'GET = "GET"

instance MethodString Symbol where
    type ToMethodString (m :: Symbol) = m

instance MethodString k => HasApiTree base (Verb (m :: k) s t a) where
    type ToApiTree base (Verb m s t a) = 'Branch '[ToMethodString m] '[]

instance HasApiTree base api => HasApiTree base (Summary s :> api) where
    type ToApiTree base (Summary s :> api) = ToApiTree base api

instance HasApiTree base api => HasApiTree base (Description s :> api) where
    type ToApiTree base (Description s :> api) = ToApiTree base api

instance HasApiTree ("<capture>" ': base) api => HasApiTree base (Capture' mods sym a :> api) where
    type ToApiTree base (Capture' mods sym a :> api) = ToApiTree ("<capture>" ': base) api

instance HasApiTree base api => HasApiTree base (QueryFlag s :> api) where
    type ToApiTree base (QueryFlag s :> api) = ToApiTree base api

instance HasApiTree base api => HasApiTree base (QueryParams s a :> api) where
    type ToApiTree base (QueryParams s a :> api) = ToApiTree base api

instance HasApiTree base api => HasApiTree base (Header' mods sym a :> api) where
    type ToApiTree base (Header' mods sym a :> api) = ToApiTree base api

type ValidApiTree api = TypeRep (ToApiTree '[] api)

validApiTree :: forall api. (HasApiTree '[] api, Typeable (ToApiTree '[] api)) => Proxy api -> ValidApiTree api
validApiTree _ = typeRep

data ApiTreeMap = BranchesMap (Set Text) (Map Text ApiTreeMap)
  deriving (Show, Eq, Ord)

reflectApiTree_ :: TypeRep (apiTree :: ApiTree) -> ApiTreeMap
reflectApiTree_ = reflectSApiTree . toSApiTree

reflectApiTree :: forall api. (HasApiTree '[] api, Typeable (ToApiTree '[] api)) => ApiTreeMap
reflectApiTree = reflectApiTree_ (typeRep @(ToApiTree '[] api))

type GoodApi = "hello" :> Get '[] ()
          :<|> "ok" :> "bye" :> Get '[] ()

validGoodApi :: ValidApiTree GoodApi
validGoodApi = validApiTree (Proxy @GoodApi)



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
reflectSSym SSym = T.pack $ symbolVal (Proxy @s)

data SApiTree :: ApiTree -> Type where
    SBranch :: Prod SSym ms -> Prod (Tup SSym SApiTree) ts -> SApiTree ('Branch ms ts)
deriving instance Show (SApiTree api)
toSApiTree :: TypeRep api -> SApiTree api
toSApiTree (App (App _ ms) ts) = unsafeCoerce $
    SBranch (toProd toSSym (unsafeCoerce ms))
            (toProd (toTup toSSym toSApiTree) (unsafeCoerce ts))

reflectSApiTree :: SApiTree api -> ApiTreeMap
reflectSApiTree (SBranch ms ts) = BranchesMap
    (S.fromAscList (reflectProd reflectSSym ms))
    (M.fromAscList (reflectProd (reflectTup reflectSSym reflectSApiTree) ts))
