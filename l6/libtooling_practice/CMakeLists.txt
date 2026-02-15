cmake_minimum_required(VERSION 3.13)
project(Practice)
set(CMAKE_CXX_STANDARD 17)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")

find_package(Clang REQUIRED CONFIG)
find_package(LLVM REQUIRED CONFIG)
include_directories(${LLVM_INCLUDE_DIRS}) 

add_executable(practice main.cpp)
target_link_libraries(practice LLVM clang-cpp)

