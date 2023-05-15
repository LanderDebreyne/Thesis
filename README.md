# Een gecombineerde calculus voor algebraïsche, scoped en parallelle effecten 

This is the repository for my masters thesis "Een gecombineerde calculus voor algebraïsche, scoped en parallelle effecten".  
The thesis presents the $\lambda_{sc}^{p}$ calculus that models the effects and handlers paradigm for algebraic, scoped and parallel effects.  

## Interpreter 

This repository contains an interpreter for the $\lambda_{sc}^{p}$ that supports typechecking.  
The following is an overview of this interpreter.

### Getting started
Make sure you have GHC and cabal installed on your device.
Navigate to the interpreter directory.
Compile the code and start the repl:

```
cd interpreter
cabal repl
```

### File structure
The interpreter consists of four main files and directory with examples

- `Syntax.hs` : implementation of the syntax, includes extra syntax for examples and type annotations
- `Evalution.hs` : implementation of the operational semantics, includes extra rules for examples and type annotations
- `Typing.hs` : implementation of a typechecking algorithm
- `Tests.hs` : a test suite with unit tests for examples and the typechecking algorithm
- `examples/scoped/...` : examples that use scoped effects
- `examples/parallel/...` : examples that use parallel effects
- `examples.combined/DepthWithAmb.hs` : an example that combines scoped and parallel effects   

### Evaluation by running examples

The interpreter provides multiple methods to evaluate computations.

- `eval` : results in a list of all intermediate computations
- `evalP` : results in a pair of the number of taken steps and the resulting computation
- `evalP'` : also results in a pair of the number of taken steps and the resulting computation but uses another evaluation function
- `evalFile` : results in saving all taken steps and intermediate computations in a file
- `evalFileFlat` : results in saving all taken steps and intermediate computations in a file and flattens nested listed and pairs in the resulting computation
- `evalFile'`: results in saving all intermediate computations in a file 
- `eval'` : results in a list of all taken steps and intermediate computations

To run examples, first start the repl.  
Then run one of the evaluation functions on the provided example computations, eg.:

```
evalFileFlat exComb
```
this results in `Return ["HHH","HHT","HTH","HTT","THH","THT","TTH","TTT"]` or all possible three letter words with `H` or `T`.

#### Scoped examples
##### Inc effect 
Incrementing a counter.  
This is actually an algebraic effect but grouped under the scoped effect directory. 

The examples increment a counter in different ways.
```
exInc1, exInc2, exInc3
```

##### Once effect
Nondeterminism with once.

Return the first result of a heads or tails.
```
exOnce
```

##### Cut effect
Nondeterminism with cut.

Return the first result of a heads or tails.
```
exCut
``` 

##### Except effect
Raising and catching exceptions.

Conditionally raise or do not raise overflow exceptions based on the value of a counter.
```
exCatch1, exCatch2, exCatch3, exCatch4, exCatch5, exCatch6, exCatch7, exCatch8
```

##### State effect
Passing, getting and putting a state.

```
exState
```

##### Depth effect
Bounded depth first search.

Bounded depth first search, taking the consumed depth in the scoped computation into account or not.
```
exDepth1, exDepth2
```

##### Parser effect
Parse a string that represents a computation with addition and multiplication and return the result.

```
exParse1, exParse2
```

##### Reader effect
Pass, get and change a local state.

```
exReader
``` 

#### Parallel examples (also implemented as scoped effects)
##### Accum effect
Pass, get and accumulate to a state.  
Accumulate a value

```
exAccum1, exAccum2, exAccum3, exAccum4, exAccum5
```

##### Weak exception effect
Throw and exception in one parallel computation, all other parallel computations continue but do not execute their continuation

```
exWeak, exWeakSc
```

##### PRNG effect
Sample a pseudo random numbers, in parallel or sequentially.

```
exPRNGpar, exPRNGseq, exPRNGparSc, exPRNGseqSc
```

##### Amb effect
Execute a computation in parallel for every input in a list of input values.
eg. find all 2 numbers that add to 13 or all 3 letter words of `H` and `T`.

```
exAmb, exComb, exAmbSc, exCombSc
```

#### Combined example: Depth with Amb
Bounded depth first search, searching all nodes in parallel using the amb effect.

```
exDepthAmb1, exDepthAmb2
```

### Evaluation by typechecking

The interpreter provides multiple methods to typecheck annotated computations.

- `typeCheckParser` : typecheck without printing intermediate results (for debugging purposes).
- `typeCheckEval` : typecheck with printing intermediate results.
- `checkFile` : typecheck and save results to a file.

#### Examples
These commands run a `checkFile` on examples of the corresponding effects
- Inc: `tInc1, tInc2, tInc3`
- Once: `tOnce`
- Cut: `tCut`
- Except: `tCatch1, tCatch2, tCatch3, tCatch4, tCatch5, tCatch6, tCatch7, tCatch8`
- State: `tState`
- Parse: `tParse1, tParse2`
- Reader: `tReader`
- Accum: `tAccum1, tAccum2, tAccum3, tAccum4`
- Weak exceptions: `tWeak1, tWeak2`
- PRNG: `tPRNG1, tPRNG2, tPRNG3, tPRNG4` 
- Amb: `tAmb, tComb, tAmbSc, tCombSc`
- DepthWithAmb `tDepthAmb1, tDepthAmb2`


### Evaluation by testing

The interpreter provides multiple tests.  

Run unit tests on all examples by running `runUnitTests`.  
Run typechecking tests on all examples by running `runTypeTests`.  
Or run both by running `runAllTests`.  

Generate files with the complete reductions, taken steps and intermediate computations by running `reductionGen reductionTestsData`.  
It is not possible to do this for the parser examples as they use Haskells built in recursion and cause infinite prints.   
(it is possible to work around this by temporarily changing the "Op", "Sc", "OpA", "ScA" show instances to not show their intermediate computations and continuation.)

