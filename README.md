# CS 426 Fall 2022 Unit Project
## Summary of Files
* CMakeLists.txt: Configures the build system for your passes. If using your
  own install of LLVM (rather than the install provided on EWS) you will need
  to modify the path on line 6 to a path to the `build/` directory of your LLVM
  install
* RegisterPasses.cpp: Provides boilerplate code needed to register the passes
  with LLVM so they can be run
* UnitLICM.h and UnitLICM.cpp: You should implement your LICM pass in these
  files. The provided code defines the `UnitLICM` class as an optimization pass
  operating on functions and acquires the results of your identification pass.
* UnitLoopInfo.h and UnitLoopInfo.cpp: You should implement your Loop Analysis
  pass in these files as well as implement the `UnitLoopInfo` class which
  provides the results of your loop analysis to your LICM pass. The provided
  code includes an empty definition of the `UnitLoopInfo` class and defines the
  `UnitLoopAnalysis` analysis and also acquires the function's `DominatorTree`
  which you are allowed to use in your analysis.
* UnitSCCP.h and UnitSCCP.cpp: You should implement your SCCP pass in these
  files. The provided code defines `UnitSCCP` as a function optimization pass.

## Build Instructions
If using your own build of LLVM, follow the above directions for modifying your
CMakeLists.txt file.

From the directory containing this file, execute the following commands
```
mkdir build
cd build
cmake ..
make
```
This should configure and then build the four passes into a single file which
can be used with LLVM's `opt` to run your passes. Note that you need to use the
version of `opt` in the `bin/` directory of the path to LLVM listed in the
CMakeLists.txt file. You can run your passes as follows:
```
opt -load-pass-plugin=libUnitProject.so -passes="unit-licm,unit-sccp" <input> -o <output>
```
You can change the string after `-passes` to specify what passes and what
order to run them in, the example above runs your LICM pass and then your SCCP
pass. You can also include LLVM built-in passes in this string. Also, note
that you may need to provide the path to the `libUnitProject.so` file if not
in the directory containing it.

Also, when compiling programs to LLVM using Clang, include `-O1` in your flags,
by default (at `-O0`) Clang disables optimizations of its generated code.
