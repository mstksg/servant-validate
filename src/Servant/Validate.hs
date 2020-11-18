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


class HasApiTree (api :: Type) where
    type ToApiTree api :: ApiTree

    sApiTree :: SApiTree (ToApiTree api)

instance (KnownSymbol path, HasApiTree api) => HasApiTree ((path :: Symbol) :> api) where
    type ToApiTree (path :> api) = 'Branch '[] '[ '(path, ToApiTree api) ]

    sApiTree = SBranch PNil (Tup SSym (sApiTree @api) :< PNil)

instance HasApiTree api => HasApiTree (Capture' mods sym a :> api) where
    type ToApiTree (Capture' mods sym a :> api) =
            'Branch '[] '[ '("<capture>", ToApiTree api) ]

    sApiTree = SBranch PNil (Tup SSym (sApiTree @api) :< PNil)

instance HasApiTree api => HasApiTree (CaptureAll sym v :> api) where
    type ToApiTree (CaptureAll sym v :> api) =
            'Branch '[] '[ '("<capture>", ToApiTree api) ]

    sApiTree = SBranch PNil (Tup SSym (sApiTree @api) :< PNil)

instance (HasApiTree a, HasApiTree b) => HasApiTree (a :<|> b) where
    type ToApiTree (a :<|> b) = MergeTree '[] (ToApiTree a) (ToApiTree b)

    sApiTree = sMergeTree @'[] (sApiTree @a) (sApiTree @b)

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

instance MethodString k => HasApiTree (Verb (m :: k) s t a) where
    type ToApiTree (Verb m s t a) = 'Branch '[ToMethodString m] '[]

instance HasApiTree api => HasApiTree (Summary s :> api) where
    type ToApiTree (Summary s :> api) = ToApiTree api

instance HasApiTree api => HasApiTree (Description s :> api) where
    type ToApiTree (Description s :> api) = ToApiTree api

instance HasApiTree api => HasApiTree (QueryFlag s :> api) where
    type ToApiTree (QueryFlag s :> api) = ToApiTree api

instance HasApiTree api => HasApiTree (QueryParams s a :> api) where
    type ToApiTree (QueryParams s a :> api) = ToApiTree api

instance HasApiTree api => HasApiTree (QueryParam' mods sym a :> api) where
    type ToApiTree (QueryParam' mods sym a :> api) = ToApiTree api

instance HasApiTree api => HasApiTree (Header' mods sym a :> api) where
    type ToApiTree (Header' mods sym a :> api) = ToApiTree api

instance HasApiTree api => HasApiTree (HttpVersion :> api) where
    type ToApiTree (HttpVersion :> api) = ToApiTree api

instance HasApiTree api => HasApiTree (Vault :> api) where
    type ToApiTree (Vault :> api) = ToApiTree api

instance HasApiTree api => HasApiTree (BasicAuth realm a :> api) where
    type ToApiTree (BasicAuth realm a :> api) = ToApiTree api

instance HasApiTree api => HasApiTree (AuthProtect tag :> api) where
    type ToApiTree (AuthProtect tag :> api) = ToApiTree api

instance HasApiTree api => HasApiTree (IsSecure :> api) where
    type ToApiTree (IsSecure :> api) = ToApiTree api

instance HasApiTree api => HasApiTree (RemoteHost :> api) where
    type ToApiTree (RemoteHost :> api) = ToApiTree api

instance HasApiTree api => HasApiTree (ReqBody' mods ct a :> api) where
    type ToApiTree (ReqBody' mods ct a :> api) = ToApiTree api

instance HasApiTree api => HasApiTree (StreamBody' mods framing ct a :> api) where
    type ToApiTree (StreamBody' mods framing ct a :> api) = ToApiTree api

type ValidApiTree api = TypeRep (ToApiTree api)

validApiTree :: forall api. (HasApiTree api, Typeable (ToApiTree api)) => Proxy api -> ValidApiTree api
validApiTree _ = typeRep

data ApiTreeMap = BranchesMap (Set Text) (Map Text ApiTreeMap)
  deriving (Show, Eq, Ord)

reflectApiTree_ :: TypeRep (apiTree :: ApiTree) -> ApiTreeMap
reflectApiTree_ = reflectSApiTree . toSApiTree

reflectApiTree :: forall api. (HasApiTree api, Typeable (ToApiTree api)) => ApiTreeMap
reflectApiTree = reflectApiTree_ (typeRep @(ToApiTree api))

type GoodApi = "hello" :> Get '[] ()
          :<|> "ok" :> "bye" :> Get '[] ()
          :<|> "ok" :> "what" :> Get '[] ()

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
reflectSSym s@SSym = T.pack $ symbolVal s

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

-- type family Compare (a :: k) (b :: k) :: Ordering
-- type instance Compare (a :: Symbol) (b :: Symbol) = CmpSymbol a b

data SOrdering :: Ordering -> Type where
    SLT :: SOrdering 'LT
    SEQ :: SOrdering 'EQ
    SGT :: SOrdering 'GT

sCases
    :: SOrdering c
    -> f lt
    -> f eq
    -> f gt
    -> f (Cases c lt eq gt)
sCases = \case
    SLT -> \lt _ _ -> lt
    SEQ -> \_ eq _ -> eq
    SGT -> \_ _ gt -> gt

compSym
    :: forall a b. ()
    => SSym a
    -> SSym b
    -> SOrdering (CmpSymbol a b)
compSym a@SSym b@SSym = case compare (symbolVal a) (symbolVal b) of
    LT -> unsafeCoerce SLT
    EQ -> unsafeCoerce SEQ
    GT -> unsafeCoerce SGT

-- sMergeSortedUnique
--     :: forall err xs ys. ()
--     => Prod SSym xs
--     -> Prod SSym ys
--     -> Prod SSym (MergeSortedUnique err xs ys)
-- sMergeSortedUnique = \case
--     PNil -> \case
--       PNil    -> PNil
--       y :< ys -> y :< ys
--     x :< xs -> \case
--       PNil    -> x :< xs
--       y :< ys -> sCases (compSym x y)
--         (x :< sMergeSortedUnique @err xs (y :< ys))
--         (error "sMergeSortedUnique: forbidden by type system")
--         (y :< sMergeSortedUnique @err (x :< xs) ys)

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
      Tup b y :< bys -> sCases (compSym a b)
        (Tup a x :< sMergePaths @base axs (Tup b y :< bys))
        (Tup a (sMergeTree @(a ': base) x y) :< sMergePaths @base axs bys)
        (Tup b y :< sMergePaths @base (Tup a x :< axs) bys)

sMergeTree :: forall base a b. SApiTree a -> SApiTree b -> SApiTree (MergeTree base a b)
sMergeTree (SBranch mA pA) (SBranch mB pB) = SBranch undefined (sMergePaths @base pA pB)
