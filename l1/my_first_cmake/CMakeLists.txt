cmake_minimum_required(VERSION 3.13)
project(helloCMake)



set(CMAKE_CXX_STANDARD 17)

find_package(Threads REQUIRED)
add_executable(hello main.cpp)

target_link_libraries(hello Threads::Threads)