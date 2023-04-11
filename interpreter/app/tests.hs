module Test where

import Examples
import Evaluation
import Syntax
import Test.HUnit

-- | Unit Test cases for results for all examples using different evaluation strategies

-- | Unit test generator for a given test and result

testCaseGen :: String -> Comp -> Comp -> [Test]
testCaseGen name test result = [TestCase (assertEqual (name ++ " NVL") (last (eval test)) result)
    , TestCase (assertEqual (name ++ " VL") (snd $ last (eval' test)) result)
    , TestCase (assertEqual (name ++ " NV") (evalP test) result)]

-- | All test

runAllTests = runTestTT $ TestList allTests
runFastTests = runTestTT $ TestList fastTests

allTests = fastTests ++ slowTests
fastTests = incTests ++ onceTests ++ cutTests ++ catchTests ++ stateTests ++ depthTests ++ readerTests ++ accumTests ++ weakExceptionTests ++ prngTests
slowTests = ambTests ++ parserTests

-- | Inc tests

runIncTests = runTestTT $ TestList incTests

incTests1 = testCaseGen "inc 1" (hOnce # runInc 0 cInc) (Return (Vlist [Vpair (Vint 0, Vint 1), Vpair (Vint 0,Vint 1)]))
incTests2 = testCaseGen "inc 2" (runInc 0 (hOnce # cInc)) (Return (Vpair (Vlist [Vint 0,Vint 1],Vint 2)))
incTests3 = testCaseGen "inc fwd" (hOnce # runInc 0 cFwd) (Return (Vlist [Vpair (Vint 1,Vint 2)]))

incTests = incTests1 ++ incTests2 ++ incTests3

-- | Once tests

runOnceTests = runTestTT $ TestList onceTests

onceTests = testCaseGen "once" (hOnce # cOnce) (Return (Vlist [Vstr "heads"]))

-- | Cut tests

runCutTests = runTestTT $ TestList cutTests

cutTests = testCaseGen "cut" (hCut # cCut) (Return (Vret (Vlist [Vstr "heads"])))

-- | Catch tests

runCatchTests = runTestTT $ TestList catchTests

catchTests = catchTests1 ++ catchTests2 ++ catchTests3 ++ catchTests4 ++ catchTests5 ++ catchTests6 ++ catchTests7 ++ catchTests8
catchTests1 = testCaseGen "catch 1" (hExcept # runInc 42 cCatch) (Return (Vsum (Right (Vpair (Vint 10,Vint 42)))))
catchTests2 = testCaseGen "catch 2" (runInc 42 (hExcept # cCatch)) (Return (Vpair (Vsum (Right (Vint 10)),Vint 43)))
catchTests3 = testCaseGen "catch 3" (hExcept # runInc 1 cCatch2) (Return (Vsum (Right (Vpair (Vstr "success", Vint 5))))) 
catchTests4 = testCaseGen "catch 4" (runInc 1 (hExcept # cCatch2)) (Return (Vpair (Vsum (Right (Vstr "success")), Vint 5)))
catchTests5 = testCaseGen "catch 5" (hExcept # runInc 8 cCatch2) (Return (Vsum (Right (Vpair (Vstr "fail", Vint 9)))))
catchTests6 = testCaseGen "catch 6" (runInc 8 (hExcept # cCatch2)) (Return (Vpair (Vsum (Right (Vstr "fail")), Vint 12)))
catchTests7 = testCaseGen "catch 7" (hExcept # runInc 42 cCatch2) (Return (Vsum (Left (Vstr "Overflow"))))
catchTests8 = testCaseGen "catch 8" (runInc 42 (hExcept # cCatch2)) (Return (Vpair (Vsum (Left (Vstr "Overflow")), Vint 43)))

-- | State tests

runStateTests = runTestTT $ TestList stateTests 

stateTests = testCaseGen "state" (handle_cState) (Return (Vpair (Vint 42,Vint 10)))

-- | Depth bounded search tests

runDepthTests = runTestTT $ TestList depthTests

depthTests = depthTests1 ++ depthTests2
depthTests1 = testCaseGen "depth 1" (Do "f" (hDepth # cDepth) $ App (Var "f" 0) (Vint 2)) (Return (Vlist [Vpair (Vint 1,Vint 1),Vpair (Vint 4,Vint 0)]))
depthTests2 = testCaseGen "depth 2" (Do "f" (hDepth2 # cDepth) $ App (Var "f" 0) (Vint 2)) (Return (Vlist [Vpair (Vint 1,Vint 0)])) 

-- | Parser tests

runParserTests = runTestTT $ TestList parserTests

parserTests = parserTests1 ++ parserTests2
parserTests1 = testCaseGen "parser 1" (handle_expr1) (Return (Vret (Vlist [Vpair (Vint 56,Vstr ""),Vpair (Vint 7,Vstr "*8")])))
parserTests2 = testCaseGen "parser 2" (handle_expr) (Return (Vret (Vlist [Vpair (Vint 56,Vstr ""),Vpair (Vint 7,Vstr "*8")])))

-- | Reader tests

runReaderTests = runTestTT $ TestList readerTests

readerTests = testCaseGen "reader" (example_cReader) (Return (Vpair (Vpair (Vlist [Vint 1,Vint 2,Vint 3,Vint 4],Vlist [Vint 1,Vint 2,Vint 3,Vint 4,Vint 5]),Vlist [Vint 1,Vint 2,Vint 3,Vint 4])))

-- | Accum tests

runAccumTests = runTestTT $ TestList accumTests

accumTests = accumTests1 ++ accumTestNoFor ++ accumTestsScoped1 ++ accumTestsScoped2 ++ accumTestNoForScoped
accumTests1 = testCaseGen "accum" (exFor) (Return (Vpair (Vint 15,Vlist [Vunit, Vunit, Vunit, Vunit, Vunit])))
accumTestNoFor = testCaseGen "accum no for" (exNoFor) (Return (Vpair (Vint 0, Vlist [Vpair (Vint 1, Vunit), Vpair (Vint 2, Vunit), Vpair (Vint 3, Vunit), Vpair (Vint 4, Vunit), Vpair (Vint 5, Vunit)])))
accumTestsScoped1 = testCaseGen "accum scoped 1" (exForSc1) (Return (Vpair (Vint 15,Vlist [Vunit, Vunit, Vunit, Vunit, Vunit])))
accumTestsScoped2 = testCaseGen "accum scoped 2" (exForSc2) (Return (Vpair (Vint 15,Vlist [Vunit, Vunit, Vunit, Vunit, Vunit]))) 
accumTestNoForScoped = testCaseGen "accum no for scoped" (exNoForSc) (Return (Vpair (Vint 0, Vlist [Vpair (Vint 1, Vunit), Vpair (Vint 2, Vunit), Vpair (Vint 3, Vunit), Vpair (Vint 4, Vunit), Vpair (Vint 5, Vunit)])))


-- | Weak exception tests

runWeakExceptionTests = runTestTT $ TestList weakExceptionTests

weakExceptionTests = weakExceptionTests1 ++ weakExceptionTestsScoped
weakExceptionTests1 = testCaseGen "weak exception" (exWeak) (Return (Vpair (Vstr "start 1!345", Vsum (Left $ Vstr "error"))))
weakExceptionTestsScoped = testCaseGen "weak exception scoped" (exWeakSc) (Return (Vpair (Vstr "start 1!345", Vsum (Left $ Vstr "error"))))


-- | PRNG tests

runPRNGTests = runTestTT $ TestList prngTests

prngTests = prngTestsPar ++ prngTestsSeq ++ prngTestsParScoped ++ prngTestsSeqScoped
prngTestsPar = testCaseGen "prng par" (exPRNGpar) (Return (Vlist [Vint 80, Vint 38, Vint 7]))
prngTestsSeq = testCaseGen "prng seq" (exPRNGseq) (Return (Vlist [Vint 48, Vint 23, Vint 95]))
prngTestsParScoped = testCaseGen "prng par scoped" (exPRNGparSc) (Return (Vlist [Vint 80, Vint 38, Vint 7]))
prngTestsSeqScoped = testCaseGen "prng seq scoped" (exPRNGseqSc) (Return (Vlist [Vint 48, Vint 23, Vint 95]))


-- | Amb tests

runAmbTests = runTestTT $ TestList ambTests

ambTests = ambTests1 ++ combTests ++ ambTestsScoped ++ combTestsScoped
ambTests1 = testCaseGen "amb" (exAmb) (Return (Vpair ( Vint 6, Vlist [ Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit]
    ])))
combTests = testCaseGen "comb" (exComb) (Return (Vlist [
            Vlist [Vlist [Vstr "HHH", Vstr "HHT"], Vlist [Vstr "HTH", Vstr "HTT"]],
            Vlist [Vlist [Vstr "THH", Vstr "THT"], Vlist [Vstr "TTH", Vstr "TTT"]]]))
ambTestsScoped = testCaseGen "amb scoped" (exAmbSc) (Return (Vpair ( Vint 6, Vlist [
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit],
        Vlist [Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit, Vunit]
    ])))
combTestsScoped = testCaseGen "comb scoped" (exCombSc) (Return (Vlist [
            Vlist [Vlist [Vstr "HHH", Vstr "HHT"], Vlist [Vstr "HTH", Vstr "HTT"]],
            Vlist [Vlist [Vstr "THH", Vstr "THT"], Vlist [Vstr "TTH", Vstr "TTT"]]]))