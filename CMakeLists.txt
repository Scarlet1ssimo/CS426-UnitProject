cmake_minimum_required(VERSION 3.13.4)
project(test-pass)

set(CMAKE_BUILD_TYPE Debug)

set(LT_LLVM_INSTALL_DIR "../llvm-14.0.0.src/build" CACHE PATH "LLVM installation directory")
list(APPEND CMAKE_PREFIX_PATH "${LT_LLVM_INSTALL_DIR}/lib/cmake/llvm/")
find_package(LLVM 14 REQUIRED CONFIG)
include_directories(SYSTEM ${LLVM_INCLUDE_DIRS})

set(CMAKE_CXX_STANDARD 14 CACHE STRING "")
if(NOT LLVM_ENABLE_RTTI)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")
endif()

add_library(UnitProject SHARED UnitLICM.cpp UnitLoopInfo.cpp UnitSCCP.cpp RegisterPasses.cpp)
