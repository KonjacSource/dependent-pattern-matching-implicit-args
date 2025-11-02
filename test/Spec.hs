module Main (main) where

import Test.Hspec
import Test.QuickCheck (property)

main :: IO ()
main = hspec $ do
  describe "示例：单元测试" $ do
    it "1 + 1 == 2" $ do
      (1 + 1) `shouldBe` (2 :: Int)

    it "head 返回第一个元素" $ do
      head [1,2,3] `shouldBe` (1 :: Int)

  describe "示例：属性测试" $ do
    it "reverse . reverse == id（针对 [Int]）" $ do
      property $ \xs -> (reverse (reverse (xs :: [Int])) == xs)

  describe "项目模块占位测试 （替换为真实测试）" $ do
    it "Common.someFunction 的行为" $ do
      pendingWith "实现 Common.someFunction 的具体测试后移除 pending"


