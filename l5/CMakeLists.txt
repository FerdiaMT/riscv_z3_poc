cmake_minimum_required(VERSION 3.13)
project(InvestigateClang)

find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

message(STATUS "=== LLVM Info ===")
message(STATUS "LLVM Version: ${LLVM_VERSION}")
message(STATUS "LLVM Include Dirs: ${LLVM_INCLUDE_DIRS}")
message(STATUS "LLVM Library Dir: ${LLVM_LIBRARY_DIRS}")
message(STATUS "LLVM Definitions: ${LLVM_DEFINITIONS}")

message(STATUS "=== Clang Info ===")
message(STATUS "Clang Include Dirs: ${CLANG_INCLUDE_DIRS}")
message(STATUS "Clang Libraries: ${CLANG_LIBS}")

add_executable(dummy dummy.cpp)