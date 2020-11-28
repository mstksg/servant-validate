{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

import Test.Hspec (hspec, describe, it)
import Test.ShouldNotTypecheck (shouldNotTypecheck)

import           Data.Proxy
import           Servant.API
import           Servant.Validate

type TestApi = "hello" :> Get '[] ()
          :<|> "ok" :> "bye" :> Get '[] ()
          :<|> "ok" :> "what" :> Get '[] ()
          :<|> "ok" :> "bye" :> Post '[] ()
          :<|> "ok" :> "bye" :> Get '[] ()

testApi :: Proxy TestApi
testApi = Proxy

validTestApi :: ValidApiTree TestApi
validTestApi = validApiTree testApi



main :: IO ()
main = hspec $ do
  describe "Servant" $ do
    it "should not allow overlapping routes" $
      shouldNotTypecheck validTestApi
