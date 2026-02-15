cmake_minimum_required(VERSION 3.13)
project(annotation_parser)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")

#find the packages
find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)
include_directories(${LLVM_INCLUDE_DIRECTORIES})

##executable
add_executable(annotationParser src/main.cpp)
target_link_libraries(annotationParser LLVM clang-cpp)