module ListTest where

testList0 :: [Bool]
testList0 = []

testList1 :: [Bool]
testList1 = [True, True, False, False]

-- testList2 :: [Bool]
-- testList2 = testList0 ++ testList1

-- testList3 :: [Bool]
-- testList3 = True : False : True : []

-- testListFunc0 :: [Bool] -> Bool
-- testListFunc0 [] = True
-- testListFunc0 [_] = False
-- testListFunc0 [_, _] = True
-- testListFunc0 (_:_:_:xs) = not (testListFunc0 xs)
