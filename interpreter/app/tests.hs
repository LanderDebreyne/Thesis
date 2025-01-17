module Test where

import DepthWithAmb
import Inc
import Once
import Cut
import Except
import State
import Depth
import Parser
import Reader
import Accum
import Weak
import Prng
import Amb
import DepthWithAmb
import Evaluation
import Syntax
import Typing
import Coins
import Test.HUnit
import qualified Data.Map as Map

data Tdata = Tdata { name :: String, testC :: Comp, result :: Comp } deriving (Show)

-- Unit Test cases for results for all examples using different evaluation strategies

-- | Unit test generator for a given test and result
testCaseGen :: String -> Comp -> Comp -> [Test]
testCaseGen name test result = [TestCase (assertEqual (name ++ " NVL") (last (eval test)) result)
    , TestCase (assertEqual (name ++ " VL") (snd $ last (eval' test)) result)
    , TestCase (assertEqual (name ++ " NV") (snd (evalP (1, test))) result)]


-- | Unit test generator for typechecking a computation
typeCheckGen :: String -> Gamma -> Sigma -> Comp -> ComputationType -> Int -> [Test]
typeCheckGen name gam sig test result n = x : y
    where x = TestCase (assertEqual (name ++ ".type_check."++ (show n)) (typeCheckC gam sig test result False) True)
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

runAllTests = runTestTT $ TestList (typeCheckTests ++ allTests) -- ^ All tests 
runUnitTests = runTestTT $ TestList allTests
runTypeTests = runTestTT $ TestList typeCheckTests
runFastTests = runTestTT $ TestList fastTests

allTests = testsFromData allTestsData
fastTests = testsFromData fastTestsData
slowTests = testsFromData slowTestsData

typeCheckTests = incTypeTests ++ onceTypeTests ++ cutTypeTests ++ catchTypeTests ++ stateTypeTests ++ depthTypeTests ++ parserTypeTests ++ readerTypeTests ++ accumTypeTests ++ weakTypeTests ++ prngTypeTests ++ ambTypeTests ++ depthAmbTypeTests

-- | List of tests from list of test data
testsFromData :: [Tdata] -> [Test]
testsFromData = concat . map (\(Tdata name test result) -> testCaseGen name test result)

allTestsData = fastTestsData ++ slowTestsData
fastTestsData = incTestsData ++ [onceTestsData] ++ coinTestsData ++ [cutTestsData] ++ catchTestsData ++ [stateTestsData] ++ depthTestsData ++ [readerTestsData] ++ accumTestsData ++ weakExceptionTestsData ++ prngTestsData ++ depthAmbTestsData
slowTestsData = parserTestsData ++ ambTestsData  

-- Parser tests do not work as reduction because parser uses haskell recursion and tries to print an infinite list
reductionTestsData = incTestsData ++ [onceTestsData] ++ coinTestsData ++ [cutTestsData] ++ catchTestsData ++ [stateTestsData] ++ depthTestsData ++ [readerTestsData] ++ accumTestsData ++ weakExceptionTestsData ++ prngTestsData ++ ambTestsData ++ depthAmbTestsData 

---------------------------------------------------------
-- | Inc tests

runIncTests = runTestTT $ TestList incTests

incTests1Data = Tdata "inc_1" exInc1 (Return (Vlist [Vpair (Vint 0, Vint 1), Vpair (Vint 0,Vint 1)]))
incTests2Data = Tdata "inc_2" exInc2 (Return (Vpair (Vlist [Vint 0,Vint 1],Vint 2)))
incTests3Data = Tdata "inc_fwd" exInc3 (Return (Vlist [Vpair (Vint 1,Vint 2)]))
incTestsData = [incTests1Data, incTests2Data, incTests3Data]
incTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) incTestsData

-- Inc typechecking 
incType1 = typeCheckGen "inc_1" tInc1Gam tInc1Sig tInc1Comp (Tlist (Tpair Tint Tint)) 1
incType2 = typeCheckGen "inc_2" tInc2Gam tInc1Sig tInc2Comp (Tpair (Tlist Tint) Tint) 1
incType3 = typeCheckGen "inc_fwd" tInc1Gam tInc3Sig tInc3Comp (Tlist (Tpair Tint Tint)) 1
incTypeTests = incType1 ++ incType2 ++ incType3

---------------------------------------------------------
-- | Once tests

runOnceTests = runTestTT $ TestList onceTests

onceTestsData = Tdata "once" exOnce (Return (Vlist [Vstr "heads"]))
onceTests = testCaseGen (name onceTestsData) (testC onceTestsData) (result onceTestsData)

-- Once typechecking
onceTypeTests = typeCheckGen "once" tOnceGam tOnceSig tOnceComp (Tlist Tstr) 1

---------------------------------------------------------
-- | Coin tests
runCoinTests = runTestTT $ TestList coinTests
coinTestData1 = Tdata "coinTrue" coinTrue (Return (Vstr "The coin flip result is heads"))
coinTestData2 = Tdata "coinBoth" coinBoth (Return (Vlist [Vstr "The coin flip result is heads", Vstr "The coin flip result is tails"])) 
coinTestData3 = Tdata "local" localState (Return (Vlist [Vpair (Vlist [Vstr "H", Vstr "H", Vstr "H"], Vint 3), 
                                                        Vpair (Vlist [Vstr "H", Vstr "T", Vstr "H", Vstr "H"], Vint 4),
                                                        Vpair (Vlist [Vstr "H", Vstr "H", Vstr "T", Vstr "H"], Vint 4),
                                                        Vpair (Vlist [Vstr "H", Vstr "H", Vstr "H", Vstr "T"], Vint 4)]))
coinTestData4 = Tdata "global" globalState (Return (Vpair (Vlist [Vlist [Vstr "H", Vstr "H", Vstr "H"],
                                                        Vlist [Vstr "H", Vstr "T", Vstr "H", Vstr "H"],
                                                        Vlist [Vstr "H", Vstr "H", Vstr "T", Vstr "H"],
                                                        Vlist [Vstr "H", Vstr "H", Vstr "H", Vstr "T"]], Vint 15)))
coinTestsData = [coinTestData1, coinTestData2, coinTestData3, coinTestData4] 
coinTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) coinTestsData

---------------------------------------------------------
-- | Cut tests

runCutTests = runTestTT $ TestList cutTests

cutTestsData = Tdata "cut" exCut (Return (Vret (Vlist [Vstr "heads"])))
cutTests = testCaseGen (name cutTestsData) (testC cutTestsData) (result cutTestsData)

-- Cut typechecking
cutTypeTests = typeCheckGen "cut" tCutGam tCutSig tCutComp (Tret (Tlist Tstr)) 1

---------------------------------------------------------
-- | Catch tests

runCatchTests = runTestTT $ TestList catchTests

catchTestsData1 = Tdata "catch_1" exCatch1 (Return (Vsum (Right (Vpair (Vint 10,Vint 42)))))
catchTestsData2 = Tdata "catch_2" exCatch2 (Return (Vpair (Vsum (Right (Vint 10)),Vint 43)))
catchTestsData3 = Tdata "catch_3" exCatch3 (Return (Vsum (Right (Vpair (Vstr "success", Vint 5)))))
catchTestsData4 = Tdata "catch_4" exCatch4 (Return (Vpair (Vsum (Right (Vstr "success")), Vint 5)))
catchTestsData5 = Tdata "catch_5" exCatch5 (Return (Vsum (Right (Vpair (Vstr "fail", Vint 9)))))
catchTestsData6 = Tdata "catch_6" exCatch6 (Return (Vpair (Vsum (Right (Vstr "fail")), Vint 12)))
catchTestsData7 = Tdata "catch_7" exCatch7 (Return (Vsum (Left (Vstr "Overflow"))))
catchTestsData8 = Tdata "catch_8" exCatch8 (Return (Vpair (Vsum (Left (Vstr "Overflow")), Vint 43)))
catchTestsData = [catchTestsData1, catchTestsData2, catchTestsData3, catchTestsData4, catchTestsData5, catchTestsData6, catchTestsData7, catchTestsData8]
catchTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) catchTestsData

-- Catch typechecking
catchType1 = typeCheckGen "catch_1" tCatchGam1 tCatchSig1 tCatchComp1 (Tsum Tstr (Tpair Tint Tint)) 1
catchType2 = typeCheckGen "catch_2" tCatchGam2 tCatchSig1 tCatchComp2 (Tpair (Tsum Tstr Tint) Tint) 1
catchType3 = typeCheckGen "catch_3" tCatchGam3 tCatchSig2 tCatchComp3 (Tsum Tstr (Tpair Tstr Tint)) 1
catchType4 = typeCheckGen "catch_4" tCatchGam4 tCatchSig2 tCatchComp4 (Tpair (Tsum Tstr Tstr) Tint) 1
catchType5 = typeCheckGen "catch_5" tCatchGam3 tCatchSig2 tCatchComp5 (Tsum Tstr (Tpair Tstr Tint)) 1
catchType6 = typeCheckGen "catch_6" tCatchGam4 tCatchSig2 tCatchComp6 (Tpair (Tsum Tstr Tstr) Tint) 1
catchType7 = typeCheckGen "catch_7" tCatchGam3 tCatchSig2 tCatchComp7 (Tsum Tstr (Tpair Tstr Tint)) 1
catchType8 = typeCheckGen "catch_8" tCatchGam4 tCatchSig2 tCatchComp8 (Tpair (Tsum Tstr Tstr) Tint) 1
catchTypeTests = catchType1 ++ catchType2 ++ catchType3 ++ catchType4 ++ catchType5 ++ catchType6 ++ catchType7 ++ catchType8

---------------------------------------------------------
-- | State tests

runStateTests = runTestTT $ TestList stateTests 

stateTestsData = Tdata "state" exState (Return (Vpair (Vint 42,Vint 10)))
stateTests = testCaseGen (name stateTestsData) (testC stateTestsData) (result stateTestsData)

-- State typechecking
stateTypeTests = typeCheckGen "state" tStateGam tStateSig handle_cStateT (Tpair Tint Tint) 1

---------------------------------------------------------
-- | Depth bounded search tests

runDepthTests = runTestTT $ TestList depthTests

depthTestsData1 = Tdata "depth_1" exDepth1 (Return (Vlist [Vpair (Vint 1,Vint 1),Vpair (Vint 4,Vint 0)]))
depthTestsData2 = Tdata "depth_2" exDepth2 (Return (Vlist [Vpair (Vint 1,Vint 0)]))
depthTestsData = [depthTestsData1, depthTestsData2]
depthTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) depthTestsData

-- Depth typechecking
depthTypeTest1 = typeCheckGen "depth_1" tDepthGam tDepthSig tDepthComp1 (Tlist (Tpair Tint Tint)) 1
depthTypeTest2 = typeCheckGen "depth_2" tDepthGam tDepthSig tDepthComp2 (Tlist (Tpair Tint Tint)) 1
depthTypeTests = depthTypeTest1 ++ depthTypeTest2

---------------------------------------------------------
-- | Parser tests

runParserTests = runTestTT $ TestList parserTests

parserTestsData1 = Tdata "parser_1" exParse1 (Return (Vret (Vlist [Vpair (Vint 56,Vstr ""),Vpair (Vint 7,Vstr "*8")])))
parserTestsData2 = Tdata "parser_2" exParse2 (Return (Vret (Vlist [Vpair (Vint 56,Vstr ""),Vpair (Vint 7,Vstr "*8")])))
parserTestsData = [parserTestsData1, parserTestsData2]
parserTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) parserTestsData

-- Parser typechecking
parserTypeTest1 = typeCheckGen "parser_1" tParseGam tParseSig handle_expr1T (Tret (Tlist (Tpair Tint Tstr))) 1
parserTypeTest2 = typeCheckGen "parser_2" tParseGam tParseSig handle_exprT (Tret (Tlist (Tpair Tint Tstr))) 1
parserTypeTests =  parserTypeTest1 ++ parserTypeTest2

---------------------------------------------------------
-- | Reader tests

runReaderTests = runTestTT $ TestList readerTests

readerTestsData = Tdata "reader" exReader (Return (Vpair (Vpair (Vlist [Vint 1,Vint 2,Vint 3,Vint 4],Vlist [Vint 1,Vint 2,Vint 3,Vint 4,Vint 5]),Vlist [Vint 1,Vint 2,Vint 3,Vint 4])))
readerTests = testCaseGen (name readerTestsData) (testC readerTestsData) (result readerTestsData)

-- Reader typechecking
readerTypeTests = typeCheckGen "reader" tReaderGam tReaderSig handle_cReaderT (Tpair (Tpair (Tlist Tint) (Tlist Tint)) (Tlist Tint)) 1

---------------------------------------------------------
-- | Accum tests

runAccumTests = runTestTT $ TestList accumTests

accumTestsData1 = Tdata "accum" exAccum1 (Return (Vpair (Vint 15,Vlist [Vunit, Vunit, Vunit, Vunit, Vunit])))
accumTestsData2 = Tdata "accum_no_for" exAccum2 (Return (Vpair (Vint 0, Vlist [Vpair (Vint 1, Vunit), Vpair (Vint 2, Vunit), Vpair (Vint 3, Vunit), Vpair (Vint 4, Vunit), Vpair (Vint 5, Vunit)])))
accumTestsData3 = Tdata "accum_scoped_1" exAccum3 (Return (Vpair (Vint 15,Vlist [Vunit, Vunit, Vunit, Vunit, Vunit])))
accumTestsData4 = Tdata "accum_scoped_2" exAccum4 (Return (Vpair (Vint 15,Vlist [Vunit, Vunit, Vunit, Vunit, Vunit])))
accumTestsData5 = Tdata "accum_no_for_scoped" exAccum5 (Return (Vpair (Vint 0, Vlist [Vpair (Vint 1, Vunit), Vpair (Vint 2, Vunit), Vpair (Vint 3, Vunit), Vpair (Vint 4, Vunit), Vpair (Vint 5, Vunit)])))
accumTestsData = [accumTestsData1, accumTestsData2, accumTestsData3, accumTestsData4, accumTestsData5]
accumTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) accumTestsData

-- Accum typechecking
accumTypeTest1 = typeCheckGen "accum" tAccumGam tAccumSig tAccumComp1 (Tpair Tint (Tlist Tunit)) 1
accumTypeTest2 = typeCheckGen "accum_no_for" tAccumGam tAccumSig tAccumComp2 (Tpair Tint (Tlist (Tpair Tint Tunit))) 1
accumTypeTest3 = typeCheckGen "accum_scoped_1" tAccumGam tAccumSigSc tAccumComp3 (Tpair Tint (Tlist Tunit)) 1
accumTypeTest4 = typeCheckGen "accum_scoped_2" tAccumGam tAccumSigSc tAccumComp4 (Tpair Tint (Tlist (Tpair Tint Tunit))) 1
accumTypeTests = accumTypeTest1 ++ accumTypeTest2 ++ accumTypeTest3 ++ accumTypeTest4

---------------------------------------------------------
-- | Weak exception tests

runWeakExceptionTests = runTestTT $ TestList weakExceptionTests

weakExceptionTestsData1 = Tdata "weak_exception_1" exWeak (Return (Vpair (Vstr "start 1!345", Vsum (Left $ Vstr "error"))))
weakExceptionTestsData2 = Tdata "weak_exception_2" exWeakSc (Return (Vpair (Vstr "start 1!345", Vsum (Left $ Vstr "error"))))
weakExceptionTestsData = [weakExceptionTestsData1, weakExceptionTestsData2]
weakExceptionTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) weakExceptionTestsData

-- Weak exception typechecking
weakTypeTest1 = typeCheckGen "weak_1" tWeakGam tWeakSig tWeakComp1 (Tpair Tstr (Tsum Tstr Tunit)) 1
weakTypeTest2 = typeCheckGen "weak_2" tWeakGam tWeakSigSc tWeakComp2 (Tpair Tstr (Tsum Tstr Tunit)) 1
weakTypeTests = weakTypeTest1 ++ weakTypeTest2

---------------------------------------------------------
-- | PRNG tests

runPRNGTests = runTestTT $ TestList prngTests

prngTestsData1 = Tdata "prng_1" exPRNGpar (Return (Vlist [Vint 80, Vint 38, Vint 7]))
prngTestsData2 = Tdata "prng_2" exPRNGseq (Return (Vlist [Vint 48, Vint 23, Vint 95]))
prngTestsData3 = Tdata "prng_3" exPRNGparSc (Return (Vlist [Vint 80, Vint 38, Vint 7]))
prngTestsData4 = Tdata "prng_4" exPRNGseqSc (Return (Vlist [Vint 48, Vint 23, Vint 95]))
prngTestsData = [prngTestsData1, prngTestsData2, prngTestsData3, prngTestsData4]
prngTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) prngTestsData

-- PRNG typechecking
prngTypeTest1 = typeCheckGen "prng_1" tPRNGGam tPRNGSig tPRNGComp1 (Tlist Tint) 1
prngTypeTest2 = typeCheckGen "prng_2" tPRNGGam tPRNGSig tPRNGComp2 (Tlist Tint) 1
prngTypeTest3 = typeCheckGen "prng_3" tPRNGGam tPRNGSigSc tPRNGComp3 (Tlist Tint) 1
prngTypeTest4 = typeCheckGen "prng_4" tPRNGGam tPRNGSigSc tPRNGComp4 (Tlist Tint) 1
prngTypeTests = prngTypeTest1 ++ prngTypeTest2 ++ prngTypeTest3 ++ prngTypeTest4

---------------------------------------------------------
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

-- Amb typechecking
ambTypeTest1 = typeCheckGen "amb_1" tAmbGam tAmbSig tAmbComp (Tpair (Tlist (Tpair Tint Tint)) (Tlist (Tlist Tunit))) 1
ambTypeTest2 = typeCheckGen "comb_1" tAmbGam tCombSig tCombComp (Nested Tstr) 1
ambTypeTest3 = typeCheckGen "amb_2" tAmbGam tAmbScSig tAmbScComp (Tpair (Tlist (Tpair Tint Tint)) (Tlist (Tlist Tunit))) 1
ambTypeTest4 = typeCheckGen "comb_2" tAmbGam tCombScSig tCombScComp (Nested Tstr) 1
ambTypeTests = ambTypeTest1 ++ ambTypeTest2 ++ ambTypeTest3 ++ ambTypeTest4

---------------------------------------------------------
-- | Depth and Amb tests

runDepthAmbTests = runTestTT $ TestList depthAmbTests

depthAmbTestsData1 = Tdata "depth_amb_1" (exDepthAmb1) (Return (Vlist [Vlist [Vlist [Vpair (Vint 1, Vint 1)], Vlist [Vlist [Vpair (Vint 4, Vint 0)], Vlist []]], Vlist []]))
depthAmbTestsData2 = Tdata "depth_amb_2" (exDepthAmb2) (Return (Vlist [Vlist [Vlist [Vpair (Vint 1, Vint 0)], Vlist []], Vlist []]))
depthAmbTestsData = [depthAmbTestsData1, depthAmbTestsData2]
depthAmbTests = concat $ map (\(Tdata name test result) -> testCaseGen name test result) depthAmbTestsData

-- Depth and Amb typechecking
depthAmbTypeTest1 = typeCheckGen "depth_amb_1" Map.empty tDepthAmbSig tDepthAmbComp1 (Nested (Tpair Tint Tint)) 1
depthAmbTypeTest2 = typeCheckGen "depth_amb_2" Map.empty tDepthAmbSig tDepthAmbComp2 (Nested (Tpair Tint Tint)) 1
depthAmbTypeTests = depthAmbTypeTest1 ++ depthAmbTypeTest2


