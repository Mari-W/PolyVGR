module Result where

type Result r = Either String r

raise :: String -> Result r
raise = Left

ok :: r -> Result r
ok = Right

todo :: Result r
todo = raise "unimplemented" 

asBool :: Result r -> Bool
asBool (Left _) = False
asBool (Right _) = True