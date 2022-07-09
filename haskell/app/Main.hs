{-# LANGUAGE ScopedTypeVariables#-}
module Main where

primes::[Int]
primes = 2:3:filter isPrime [5,7..] :: [Int]
isPrime:: Int-> Bool
isPrime x = foldr (&&) True map2
  where
    map2 = map (\n -> (x `rem` n) /= 0) take1
    take1 = takeWhile ( \n -> ((n^2) <= x)) primes
main = print . length . takeWhile (<= 2^24) $ primes
