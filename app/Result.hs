module Result where

type Result r = Either String r

raise :: String -> Result r
raise = Left

ok :: r -> Result r
ok = Right

todo :: Result r
todo = raise "unimplemented" 

unreachable :: Result r
unreachable = raise "unreachable"