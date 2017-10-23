# CMakeLists files in this project can
cmake_minimum_required (VERSION 2.8.11)
project (P8MVM)

# Recurse into the "initiation" and "reaction" subdirectories. This does not actually
# cause another cmake executable to run. The same process will walk through
# the project's entire directory structure.
#add_subdirectory (src/initiation)
#add_subdirectory (src/reaction)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
set(SOURCE_FILES ./src/reaction/reaction.cpp)
add_executable(Polymerization ${SOURCE_FILES})

