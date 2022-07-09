cmake_minimum_required(VERSION 3.14)
project(ustring)
set(CMAKE_CXX_STANDARD 20)

add_executable(test_ustring test_ustring.cpp check_inline.cpp ustring.h)

