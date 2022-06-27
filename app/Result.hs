module Result where

type Result r = Either String r

raise :: String -> Result r
raise = Left

ok :: r -> Result r
ok = Right