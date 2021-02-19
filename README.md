# servant-validate

A package with "test suites" to help verify that your servant APIs are valid at
compile-time.

Currently the only property tested is that there are no duplicated paths.

```haskell
data DeadlySinEnum = Lust | Gluttony | Greed | Sloth | Wrath | Envy | Pride

type MathApi  = "sin" :> ReqBody '[JSON] Double        :> Post '[JSON] NoContent
type SatanApi = "sin" :> ReqBody '[JSON] DeadlySinEnum :> Post '[JSON] NoContent

type MyApi = MathApi :<|> SatanApi

myApi :: Proxy MyApi
myApi = Proxy

validMyApi :: ValidApiTree MyApi
validMyApi = validApiTree myApi
```

```haskell
warning: [-Wdeferred-type-errors]
    • Duplicate method in API at path /sin: "POST"
    • In the expression: validApiTree myApi
      In an equation for ‘validMyApi’: validMyApi = validApiTree myApi
```
