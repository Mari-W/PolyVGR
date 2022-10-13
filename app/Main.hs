module Main where

import Ast
import Kinding
import Typing
import Pretty 

t1 = EAll "c" (KDom SHSingle) [] (
      EAll "s" KSession [] (
        EArr SSEmpty EUnit [] SSEmpty  (
          EArr (SSBind (TVar "c") (SSend "d" (KDom SHEmpty) SSEmpty EUnit (TVar "s"))) (EChan (TVar "c")) [] (SSBind (TVar "c") (TVar "s"))  
            EUnit
        )
      )
    )

t2 = EAll "n1" KShape [] (
      EAll "ss1" (KLam (KDom (TVar "n1")) KState) [] (
        EAll "n2" KShape [] (
          EAll "n" KShape [] (
            EAll "ss2" (KLam (KDom (SHMerge (TVar "n") (TVar "n2"))) KState) [] (
              EAll "t2" (KLam (KDom (SHMerge (TVar "n") (TVar "n2"))) KType) [] (
                EAll "a1" (KDom (TVar "n1")) [] (
                  EAll "a2" (KDom  (TVar "n2")) [] (
                    EAll "g" (KDom SHSingle) [(TVar  "a1", TVar "g"), (TVar  "a2", TVar "g")] (
                      EAll "s" KSession [] (
                        EAll "s1" KSession [] (
                          EArr SSEmpty (
                            EArr (
                              SSMerge (TApp (TVar "ss1") (TVar "a1")) (SSBind (TVar "g") (TVar "s"))
                            ) (EChan (TVar "g")) [("a", HasKind (KDom (TVar "n")))] (
                              SSMerge (TApp (TVar "ss2") (DMerge (TVar "a") (TVar "a2"))) (SSBind (TVar "g") (TVar "s1"))
                            ) (TApp (TVar "t2") (DMerge (TVar "a") (TVar "a2")))
                          ) [] SSEmpty (
                            EArr (
                              SSMerge (TApp (TVar "ss1") (TVar "a1")) (SSBind (TVar "g") (SSend "_" (KDom SHEmpty) SSEmpty EUnit (TVar "s")))
                            ) (EChan (TVar "g")) [("a", HasKind (KDom (TVar "n")))] (
                              SSMerge (TApp (TVar "ss2") (DMerge (TVar "a") (TVar "a2"))) (SSBind (TVar "g") (TVar "s1"))
                            ) (TApp (TVar "t2") (DMerge (TVar "a") (TVar "a2")))
                          )                      
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

t3 = EAll "n" KShape [] (
      EAll "a" (KDom (TVar "n")) [] (
        EAll "ss" (KLam (KDom (TVar "n")) KState) [] (
          EAll "t" (KLam (KDom (TVar "n")) KType) [] (
            EAll "c" (KDom SHSingle ) [(TVar "a", TVar "c")] (
              EAll "s" KSession [] (
                EArr SSEmpty (TApp (TVar "t") (TVar "a")) [] SSEmpty (
                  EArr (
                    SSMerge (TApp (TVar "ss") (TVar "a")) (SSBind (TVar "c") (
                      SSend "a" (KDom (TVar "n")) (TApp (TVar "ss") (TVar "a")) (TApp (TVar "t") (TVar "a")) (TVar "s")
                    )
                   )
                  ) (EChan (TVar "c")) [] (SSBind (TVar "c") (TVar "s")) EUnit 
                )
              )
            )
          )
        )
      )
    ) 

v11 = VTAbs "c" (KDom SHEmpty) [] (
        VTAbs "s" KSession [] (
          VAbs SSEmpty  "x" EUnit (
            Val (VAbs (SSBind (TVar "c") (
              SSend "a" (KDom SHEmpty) SSEmpty EUnit (TVar "s")
            )) "y" (EChan (TVar "c")) (
              Send (VVar "x") (VVar "y")
            ))
          )
        )
      )

main :: IO ()
main = case typeV' [] v11 of   
  Left s -> putStrLn $ "TYPE ERROR\n" ++ s
  Right ki -> putStrLn (pretty ki)
