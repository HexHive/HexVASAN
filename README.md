# HexVASAN: Venerable Variadic Vulnerabilities Vanquished
Recommended LLVM version is 3.9.1 
## To build:
### Step 1: `git clone https://github.com/HexHive/HexVASAN.git`
### Step 2: Now in your llvm working directory, do the following steps

```
  - rm /path/to/llvm/tools/clang/lib/Driver/Tools.cpp 
    ln -s /path/to/HexVASAN/src/Tools.cpp /path/to/llvm/tools/clang/lib/Driver/Tools.cpp 
    
  - rm /path/to/llvm/tools/clang/include/clang/Basic/Sanitizers.def
    ln -s /path/to/HexVASAN/src/Sanitizers.def /path/to/llvm/tools/clang/include/clang/Basic/Sanitizers.def
    
  - rm /path/to/llvm/tools/clang/include/clang/Driver/SanitizerArgs.h
    ln -s /path/to/HexVASAN/src/SanitizerArgs.h /path/to/llvm/tools/clang/include/clang/Driver/SanitizerArgs.h
    
  - rm /path/to/llvm/include/llvm/Transforms/Instrumentation.h 
    ln -s /path/to/HexVASAN/src/Instrumentation.h /path/to/llvm/include/llvm/Transforms/Instrumentation.h
    
  - rm /path/to/llvm/include/llvm/InitializePasses.h
    ln -s /path/to/HexVASAN/src/InitializePasses.h /path/to/llvm/include/llvm/InitializePasses.h
    
  - rm /path/to/llvm/tools/clang/lib/CodeGen/BackendUtil.cpp
    ln -s /path/to/HexVASAN/src/BackendUtil.cpp /path/to/llvm/tools/clang/lib/CodeGen/BackendUtil.cpp
 ```
    
 ### Step 3: 
 a. Now link the two compiler passes
 
 ```
 ln -s /path/to/HexVASAN/lib/Transforms/Instrumentation/VASAN.cpp path/to/llvm/lib/Transforms/Instrumentation/VASAN.cpp
 ln -s /path/to/HexVASAN/lib/Transforms/Instrumentation/VASANCaller.cpp path/to/llvm/lib/Transforms/Instrumentation/VASANCaller.cpp
 ```
 
 b. Now add VASAN.cpp and VASANCaller.cpp in the CMakeLists.txt in path/to/llvm/lib/Transforms/Instrumentation/
    
 ### Step 4: 
 a. Now add the runtime library
 ```
 ln -s /path/to/HexVASAN/runtime/vasan  /path/to/llvm/projects/compiler-rt/lib/vasan
 ```
 b. Add the following line in the  CMakeLists.txt at /path/to/llvm/projects/compiler-rt/lib/
  ```
  add_subdirectory(vasan)
  ```
 ### Step 5: cmake option for build 
 ```
 cmake -GNinja \
-DCMAKE_BUILD_TYPE=Release \
-DCMAKE_C_COMPILER=clang \
-DCMAKE_CXX_COMPILER=clang++ \
-DLLVM_ENABLE_ASSERTIONS=ON \
-DLLVM_BUILD_TESTS=OFF \
-DLLVM_BUILD_EXAMPLES=OFF \
-DLLVM_INCLUDE_TESTS=OFF \
-DLLVM_INCLUDE_EXAMPLES=OFF \
-DBUILD_SHARED_LIBS=on \
-DLLVM_TARGETS_TO_BUILD="X86" \
-DCMAKE_C_FLAGS="-fstandalone-debug" \
-DCMAKE_CXX_FLAGS="-fstandalone-debug" \
 ../llvm
```
### Step 6: 
Build command
```
ninja
```

## Run
a. To run, give the following command:
```
$BUILD_DIR/bin/clang++ test.cpp -fsanitize=vasan
./a.out
```
b. Alternatively, you can set the error log file and run with backtracing enabled
```
export VASAN_ERR_LOG_PATH="/tmp/vasan/"
$BUILD_DIR/bin/clang++ test.cpp -fsanitize=vasan-backtrace
./a.out
```
