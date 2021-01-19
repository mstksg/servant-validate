{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeOperators          #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

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

data DeadlySinEnum = Lust | Gluttony | Greed | Sloth | Wrath | Envy | Pride

type MathApi  = "sin" :> ReqBody '[JSON] Double        :> Post '[JSON] NoContent
type SatanApi = "sin" :> ReqBody '[JSON] DeadlySinEnum :> Post '[JSON] NoContent

type MyApi = MathApi :<|> SatanApi

myApi :: Proxy MyApi
myApi = Proxy

validMyApi :: ValidApiTree MyApi
validMyApi = validApiTree myApi

main :: IO ()
main = hspec $ do
  describe "Servant" $ do
    it "should not allow overlapping routes" $
      shouldNotTypecheck validMyApi
    it "should not allow overlapping routes (nested)" $
      shouldNotTypecheck validTestApi
