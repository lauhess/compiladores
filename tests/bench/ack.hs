module Main where

data P = P !Int !Int

main :: IO ()
main = print $ ack (P 3 8) id
  where
    ack :: P -> (Int -> Int) -> Int
    ack (P 0 n) k = k (n + 1)
    ack (P m 0) k = ack (P (m-1) 1) k
    ack (P m n) k = ack (P m (n-1)) (\a -> ack (P (m-1) a) k)