cmake_minimum_required(VERSION 3.20)

project(TurochampCPP LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_executable(turochamp_cpp main.cpp)

if(MSVC)
    target_compile_options(turochamp_cpp PRIVATE /W4)
else()
    target_compile_options(turochamp_cpp PRIVATE -Wall -Wextra -pedantic)
endif()
