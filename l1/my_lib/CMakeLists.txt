cmake_minimum_required(VERSION 3.13)
project(libTest)

set(CMAKE_CXX_STANDARD 17)

add_executable(app main.cpp)

target_include_directories(app PRIVATE include/)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -O3")