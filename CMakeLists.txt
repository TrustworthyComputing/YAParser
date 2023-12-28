cmake_minimum_required(VERSION 3.13)  # CMake version check
project(Parser)               # Create project "simple_example"
set(CMAKE_CXX_STANDARD 14)            # Enable c++14 standard

# Add main.cpp file of the project root directory as a source file
set(SOURCE_FILES parse.cpp)


find_package(Boost 1.80.0)
if(Boost_FOUND)
    include_directories(${Boost_INCLUDE_DIRS})
    add_executable(Parser ${SOURCE_FILES})
endif()
