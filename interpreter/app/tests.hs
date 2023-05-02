module Test where

import Examples
import CombExamples
import TypedExamples
import Evaluation
import Syntax
import Typing
import Test.HUnit
import qualified Data.Map as Map

data Tdata = Tdata { name :: String, testC :: Comp, result :: Comp } deriving (Show)

-- | Unit Test cases for results for all examples using different evaluation strategies

-- | Unit test generator for a given test and result

testCaseGen :: String -> Comp -> Comp -> [Test]
testCaseGen name test result = [TestCase (assertEqual (name ++ " NVL") (last (eval test)) result)
    , TestCase (assertEqual (name ++ " VL") (snd $ last (eval' test)) result)
    , TestCase (assertEqual (name ++ " NV") (evalP test) result)]


-- | Unit test generator for typechecking a computation

typeCheckGen :: String -> Gamma -> Sigma -> Comp -> ComputationType -> Int -> [Test]
typeCheckGen name gam sig test result n = x : y
    where x = TestCase (assertEqual (name ++ ".type_check."++ (show n)) (typeCheckC gam sig test result) True)
          y = case (eval1' test) of
            (step, Just c') -> typeCheckGen name gam sig c' result (n+1)
            (step, Nothing) -> []


-- | Reduction generator for given list of Tests

reductionGen :: [Tdata] -> IO ()
reductionGen [] = return ()
reductionGen ((Tdata name comp _):xs) = do
    let steps = eval' comp
    writeFile ("reductions/" ++ name) (prettyprint steps 1)
    reductionGen xs

-- | All test

runAllTests = runTestTT $ TestList (typeCheckTests ++ allTests)
runFastTests = runTestTT $ TestList fastTests

allTests = testsFromData allTestsData
fastTests = testsFromData fastTestsData
slowTests = testsFromData slowTestsData

typeCheckTests = incTypeTests ++ onceTypeTests

testsFromData :: [Tdata] -> [Test]
testsFromData = concat . map (\(Tdata name test result) -> testCaseGen name test result)

allTestsData = fastTestsData ++ slowTestsData
fastTestsData = incTestsData ++ [onceTestsData] ++ [cutTestsData] ++ catchTestsData ++ [stateTestsData] ++ depthTestsData ++ [readerTestsData] ++ accumTestsData ++ weakExceptionTestsData ++ prngTestsData ++ depthAmbTestsData
slowTestsData = ambTestsData ++ parserTestsData 

-- Parser and reader tests do not work as reduction because parser uses haskell recursion and tries to print an infinite list
reductionTestsData = incTestsData ++ [onceTestsData] ++ [cutTestsData] ++ catchTestsData ++ [stateTestsData] ++ depthTestsData ++ accumTestsData ++ weakExceptionTestsData ++ prngTestsData ++ ambTestsData

-- | Inc tests

runIncTests = runTestTT $ TestList incTests

incTests1Data = Tdata "inc_1" (hOnce # runInc 0 cInc) (Return (Vlist [Vpair (Vint 0, Vint 1), Vpair (Vint 0,Vint 1)]))
incTests2Data = Tdata "inc_2" (runInc 0 (hOnce # cInc)) (Return (Vpair (Vlist [Vint 0,Vint 1],Vint 2)))
incTests3Data = Tdata "inc_fwd" (hOnce # runInc 0 cFwd) (Return (Vlist [Vpair (Vint 1,Vint 2)]))
incTestsData = [incTests1Data, incTests2Data, incTests3Data]
incTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) incTestsData

-- Inc typechecking 
incType1 = typeCheckGen "inc_1" tInc1Gam tInc1Sig tInc1Comp (Tlist (Tpair Tint Tint)) 1
incType2 = typeCheckGen "inc_2" tInc2Gam tInc1Sig tInc2Comp (Tpair (Tlist Tint) Tint) 1
incType3 = typeCheckGen "inc_fwd" tInc1Gam tInc3Sig tInc3Comp (Tlist (Tpair Tint Tint)) 1
incTypeTests = incType1 ++ incType2 ++ incType3

-- | Once tests

runOnceTests = runTestTT $ TestList onceTests

onceTestsData = Tdata "once" (hOnce # cOnce) (Return (Vlist [Vstr "heads"]))
onceTests = testCaseGen (name onceTestsData) (testC onceTestsData) (result onceTestsData)

-- Once typechecking
onceTypeTests = typeCheckGen "once" tOnceGam tOnceSig tOnceComp (Tlist Tstr) 1

-- | Cut tests

runCutTests = runTestTT $ TestList cutTests

cutTestsData = Tdata "cut" (hCut # cCut) (Return (Vret (Vlist [Vstr "heads"])))
cutTests = testCaseGen (name cutTestsData) (testC cutTestsData) (result cutTestsData)

-- | Catch tests

runCatchTests = runTestTT $ TestList catchTests

catchTestsData1 = Tdata "catch_1" (hExcept # runInc 42 cCatch) (Return (Vsum (Right (Vpair (Vint 10,Vint 42)))))
catchTestsData2 = Tdata "catch_2" (runInc 42 (hExcept # cCatch)) (Return (Vpair (Vsum (Right (Vint 10)),Vint 43)))
catchTestsData3 = Tdata "catch_3" (hExcept # runInc 1 cCatch2) (Return (Vsum (Right (Vpair (Vstr "success", Vint 5)))))
catchTestsData4 = Tdata "catch_4" (runInc 1 (hExcept # cCatch2)) (Return (Vpair (Vsum (Right (Vstr "success")), Vint 5)))
catchTestsData5 = Tdata "catch_5" (hExcept # runInc 8 cCatch2) (Return (Vsum (Right (Vpair (Vstr "fail", Vint 9)))))
catchTestsData6 = Tdata "catch_6" (runInc 8 (hExcept # cCatch2)) (Return (Vpair (Vsum (Right (Vstr "fail")), Vint 12)))
catchTestsData7 = Tdata "catch_7" (hExcept # runInc 42 cCatch2) (Return (Vsum (Left (Vstr "Overflow"))))
catchTestsData8 = Tdata "catch_8" (runInc 42 (hExcept # cCatch2)) (Return (Vpair (Vsum (Left (Vstr "Overflow")), Vint 43)))
catchTestsData = [catchTestsData1, catchTestsData2, catchTestsData3, catchTestsData4, catchTestsData5, catchTestsData6, catchTestsData7, catchTestsData8]
catchTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) catchTestsData

-- | State tests

runStateTests = runTestTT $ TestList stateTests 

stateTestsData = Tdata "state" (handle_cState) (Return (Vpair (Vint 42,Vint 10)))
stateTests = testCaseGen (name stateTestsData) (testC stateTestsData) (result stateTestsData)

-- | Depth bounded search tests

runDepthTests = runTestTT $ TestList depthTests

depthTestsData1 = Tdata "depth_1" (Do "f" (hDepth # cDepth) $ App (Var "f" 0) (Vint 2)) (Return (Vlist [Vpair (Vint 1,Vint 1),Vpair (Vint 4,Vint 0)]))
depthTestsData2 = Tdata "depth_2" (Do "f" (hDepth2 # cDepth) $ App (Var "f" 0) (Vint 2)) (Return (Vlist [Vpair (Vint 1,Vint 0)]))
depthTestsData = [depthTestsData1, depthTestsData2]
depthTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) depthTestsData

-- | Parser tests

runParserTests = runTestTT $ TestList parserTests

parserTestsData1 = Tdata "parser_1" (handle_expr1) (Return (Vret (Vlist [Vpair (Vint 56,Vstr ""),Vpair (Vint 7,Vstr "*8")])))
parserTestsData2 = Tdata "parser_2" (handle_expr) (Return (Vret (Vlist [Vpair (Vint 56,Vstr ""),Vpair (Vint 7,Vstr "*8")])))
parserTestsData = [parserTestsData1, parserTestsData2]
parserTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) parserTestsData

-- | Reader tests

runReaderTests = runTestTT $ TestList readerTests

readerTestsData = Tdata "reader" (example_cReader) (Return (Vpair (Vpair (Vlist [Vint 1,Vint 2,Vint 3,Vint 4],Vlist [Vint 1,Vint 2,Vint 3,Vint 4,Vint 5]),Vlist [Vint 1,Vint 2,Vint 3,Vint 4])))
readerTests = testCaseGen (name readerTestsData) (testC readerTestsData) (result readerTestsData)

-- | Accum tests

runAccumTests = runTestTT $ TestList accumTests

accumTestsData1 = Tdata "accum" (exFor) (Return (Vpair (Vint 15,Vlist [Vunit, Vunit, Vunit, Vunit, Vunit])))
accumTestsData2 = Tdata "accum_no_for" (exNoFor) (Return (Vpair (Vint 0, Vlist [Vpair (Vint 1, Vunit), Vpair (Vint 2, Vunit), Vpair (Vint 3, Vunit), Vpair (Vint 4, Vunit), Vpair (Vint 5, Vunit)])))
accumTestsData3 = Tdata "accum_scoped_1" (exForSc1) (Return (Vpair (Vint 15,Vlist [Vunit, Vunit, Vunit, Vunit, Vunit])))
accumTestsData4 = Tdata "accum_scoped_2" (exForSc2) (Return (Vpair (Vint 15,Vlist [Vunit, Vunit, Vunit, Vunit, Vunit])))
accumTestsData5 = Tdata "accum_no_for_scoped" (exNoForSc) (Return (Vpair (Vint 0, Vlist [Vpair (Vint 1, Vunit), Vpair (Vint 2, Vunit), Vpair (Vint 3, Vunit), Vpair (Vint 4, Vunit), Vpair (Vint 5, Vunit)])))
accumTestsData = [accumTestsData1, accumTestsData2, accumTestsData3, accumTestsData4, accumTestsData5]
accumTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) accumTestsData

-- | Weak exception tests

runWeakExceptionTests = runTestTT $ TestList weakExceptionTests

weakExceptionTestsData1 = Tdata "weak_exception_1" (exWeak) (Return (Vpair (Vstr "start 1!345", Vsum (Left $ Vstr "error"))))
weakExceptionTestsData2 = Tdata "weak_exception_2" (exWeakSc) (Return (Vpair (Vstr "start 1!345", Vsum (Left $ Vstr "error"))))
weakExceptionTestsData = [weakExceptionTestsData1, weakExceptionTestsData2]
weakExceptionTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) weakExceptionTestsData

-- | PRNG tests

runPRNGTests = runTestTT $ TestList prngTests

prngTestsData1 = Tdata "prng_1" (exPRNGpar) (Return (Vlist [Vint 80, Vint 38, Vint 7]))
prngTestsData2 = Tdata "prng_2" (exPRNGseq) (Return (Vlist [Vint 48, Vint 23, Vint 95]))
prngTestsData3 = Tdata "prng_3" (exPRNGparSc) (Return (Vlist [Vint 80, Vint 38, Vint 7]))
prngTestsData4 = Tdata "prng_4" (exPRNGseqSc) (Return (Vlist [Vint 48, Vint 23, Vint 95]))
prngTestsData = [prngTestsData1, prngTestsData2, prngTestsData3, prngTestsData4]
prngTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) prngTestsData

-- | Amb tests

runAmbTests = runTestTT $ TestList ambTests

ambTestsData1 = Tdata "amb_1" (exAmb) (Return (Vpair ( Vlist [Vpair (Vint 4, Vint 9), Vpair (Vint 5, Vint 8), Vpair (Vint 6, Vint 7), Vpair (Vint 7, Vint 6), Vpair (Vint 8, Vint 5), Vpair (Vint 9, Vint 4)],
    Vlist [ Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit]])))
ambTestsData2 = Tdata "amb_2" (exAmbSc) (Return (Vpair ( Vlist [Vpair (Vint 4, Vint 9), Vpair (Vint 5, Vint 8), Vpair (Vint 6, Vint 7), Vpair (Vint 7, Vint 6), Vpair (Vint 8, Vint 5), Vpair (Vint 9, Vint 4)],
    Vlist [ Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
            Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit]])))
combTestsData1 = Tdata "comb_1" (exComb) (Return (Vlist [
            Vlist [Vlist [Vstr "HHH", Vstr "HHT"], Vlist [Vstr "HTH", Vstr "HTT"]],
            Vlist [Vlist [Vstr "THH", Vstr "THT"], Vlist [Vstr "TTH", Vstr "TTT"]]]))
combTestsData2 = Tdata "comb_2" (exCombSc) (Return (Vlist [
            Vlist [Vlist [Vstr "HHH", Vstr "HHT"], Vlist [Vstr "HTH", Vstr "HTT"]],
            Vlist [Vlist [Vstr "THH", Vstr "THT"], Vlist [Vstr "TTH", Vstr "TTT"]]]))
ambTestsData = [ambTestsData1, ambTestsData2, combTestsData1, combTestsData2]
ambTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) ambTestsData 


-- | Depth and Amb tests

runDepthAmbTests = runTestTT $ TestList depthAmbTests

depthAmbTestsData1 = Tdata "depth_amb_1" (exDepthAmb1) (Return (Vlist [Vlist [Vlist [Vpair (Vint 1, Vint 1)], Vlist [Vlist [Vpair (Vint 4, Vint 0)], Vlist []]], Vlist []]))
depthAmbTestsData2 = Tdata "depth_amb_2" (exDepthAmb2) (Return (Vlist [Vlist [Vlist [Vpair (Vint 1, Vint 0)], Vlist []], Vlist []]))
depthAmbTestsData = [depthAmbTestsData1, depthAmbTestsData2]
depthAmbTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) depthAmbTestsData