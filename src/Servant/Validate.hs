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

module Servant.Validate
  ( HasApiTree(..), MethodString(..)
  , validApiTree, ValidApiTree
  , reflectApiTree, reflectApiTree_
  , SApiTree(..), reflectSApiTree
  ) where

import           Data.Kind
import           Data.Map                  (Map)
import           Data.Proxy
import           Data.Set                  (Set)
import           Data.Text                 (Text)
import           Data.Type.Bool
import           Data.Type.Equality
import           GHC.TypeLits
import           Servant.API
import           Servant.Validate.Internal
import           Type.Reflection
import           Unsafe.Coerce
import qualified Data.Map                  as M
import qualified Data.Set                  as S
import qualified Data.Text                 as T

-- | Has a valid well-formed API Tree
class HasApiTree (api :: Type) where
    type ToApiTree api :: ApiTree

    -- | Useful runtime witness of the API tree; use to inspect it with
    -- 'reflectApiTree'.  This is not used in any part of the actual
    -- validation; is just an extra treat.
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

instance (MethodString k, KnownSymbol (ToMethodString m)) => HasApiTree (Verb (m :: k) s t a) where
    type ToApiTree (Verb m s t a) = 'Branch '[ToMethodString m] '[]
    sApiTree = SBranch (SSym :< PNil) PNil

instance HasApiTree api => HasApiTree (Summary s :> api) where
    type ToApiTree (Summary s :> api) = ToApiTree api
    sApiTree = sApiTree @api

instance HasApiTree api => HasApiTree (Description s :> api) where
    type ToApiTree (Description s :> api) = ToApiTree api
    sApiTree = sApiTree @api

instance HasApiTree api => HasApiTree (QueryFlag s :> api) where
    type ToApiTree (QueryFlag s :> api) = ToApiTree api
    sApiTree = sApiTree @api

instance HasApiTree api => HasApiTree (QueryParams s a :> api) where
    type ToApiTree (QueryParams s a :> api) = ToApiTree api
    sApiTree = sApiTree @api

instance HasApiTree api => HasApiTree (QueryParam' mods sym a :> api) where
    type ToApiTree (QueryParam' mods sym a :> api) = ToApiTree api
    sApiTree = sApiTree @api

instance HasApiTree api => HasApiTree (Header' mods sym a :> api) where
    type ToApiTree (Header' mods sym a :> api) = ToApiTree api
    sApiTree = sApiTree @api

instance HasApiTree api => HasApiTree (HttpVersion :> api) where
    type ToApiTree (HttpVersion :> api) = ToApiTree api
    sApiTree = sApiTree @api

instance HasApiTree api => HasApiTree (Vault :> api) where
    type ToApiTree (Vault :> api) = ToApiTree api
    sApiTree = sApiTree @api

instance HasApiTree api => HasApiTree (BasicAuth realm a :> api) where
    type ToApiTree (BasicAuth realm a :> api) = ToApiTree api
    sApiTree = sApiTree @api

instance HasApiTree api => HasApiTree (AuthProtect tag :> api) where
    type ToApiTree (AuthProtect tag :> api) = ToApiTree api
    sApiTree = sApiTree @api

instance HasApiTree api => HasApiTree (IsSecure :> api) where
    type ToApiTree (IsSecure :> api) = ToApiTree api
    sApiTree = sApiTree @api

instance HasApiTree api => HasApiTree (RemoteHost :> api) where
    type ToApiTree (RemoteHost :> api) = ToApiTree api
    sApiTree = sApiTree @api

instance HasApiTree api => HasApiTree (ReqBody' mods ct a :> api) where
    type ToApiTree (ReqBody' mods ct a :> api) = ToApiTree api
    sApiTree = sApiTree @api

instance HasApiTree api => HasApiTree (StreamBody' mods framing ct a :> api) where
    type ToApiTree (StreamBody' mods framing ct a :> api) = ToApiTree api
    sApiTree = sApiTree @api

-- | To be used with 'validApiTree'.
type ValidApiTree api = TypeRep (ToApiTree api)

-- | The full validator.  To use:
--
-- @
-- serverApi :: Proxy ServerApi
-- serverApi = Proxy
--
-- validServerApi :: ValidApiTree ServerApi
-- validServerApi = validApiTree serverApi
-- @
validApiTree :: forall api. (HasApiTree api, Typeable (ToApiTree api)) => Proxy api -> ValidApiTree api
validApiTree _ = typeRep

data ApiTreeMap = BranchesMap (Set Text) (Map Text ApiTreeMap)
  deriving (Show, Eq, Ord)

-- | Version of 'reflectApiTree' taking an explicit 'TypeRep'.
reflectApiTree_ :: TypeRep (apiTree :: ApiTree) -> ApiTreeMap
reflectApiTree_ = reflectSApiTree . toSApiTree

-- | Useful utility to view the routing structure of a tree; similar to
-- 'Servant.Server.layout'.
reflectApiTree :: forall api. (HasApiTree api, Typeable (ToApiTree api)) => ApiTreeMap
reflectApiTree = reflectApiTree_ (typeRep @(ToApiTree api))

reflectSApiTree :: SApiTree api -> ApiTreeMap
reflectSApiTree (SBranch ms ts) = BranchesMap
    (S.fromAscList (reflectProd reflectSSym ms))
    (M.fromAscList (reflectProd (reflectTup reflectSSym reflectSApiTree) ts))
