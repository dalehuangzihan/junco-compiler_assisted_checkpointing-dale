# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.22

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/dalehuang/Documents/llvm-dale

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/dalehuang/Documents/llvm-dale/build

# Include any dependencies generated for this target.
include lib/CMakeFiles/DuplicateBB.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include lib/CMakeFiles/DuplicateBB.dir/compiler_depend.make

# Include the progress variables for this target.
include lib/CMakeFiles/DuplicateBB.dir/progress.make

# Include the compile flags for this target's objects.
include lib/CMakeFiles/DuplicateBB.dir/flags.make

lib/CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.o: lib/CMakeFiles/DuplicateBB.dir/flags.make
lib/CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.o: ../lib/DuplicateBB.cpp
lib/CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.o: lib/CMakeFiles/DuplicateBB.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/dalehuang/Documents/llvm-dale/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object lib/CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.o"
	cd /home/dalehuang/Documents/llvm-dale/build/lib && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT lib/CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.o -MF CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.o.d -o CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.o -c /home/dalehuang/Documents/llvm-dale/lib/DuplicateBB.cpp

lib/CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.i"
	cd /home/dalehuang/Documents/llvm-dale/build/lib && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/dalehuang/Documents/llvm-dale/lib/DuplicateBB.cpp > CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.i

lib/CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.s"
	cd /home/dalehuang/Documents/llvm-dale/build/lib && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/dalehuang/Documents/llvm-dale/lib/DuplicateBB.cpp -o CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.s

# Object files for target DuplicateBB
DuplicateBB_OBJECTS = \
"CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.o"

# External object files for target DuplicateBB
DuplicateBB_EXTERNAL_OBJECTS =

lib/libDuplicateBB.so: lib/CMakeFiles/DuplicateBB.dir/DuplicateBB.cpp.o
lib/libDuplicateBB.so: lib/CMakeFiles/DuplicateBB.dir/build.make
lib/libDuplicateBB.so: lib/CMakeFiles/DuplicateBB.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/dalehuang/Documents/llvm-dale/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX shared library libDuplicateBB.so"
	cd /home/dalehuang/Documents/llvm-dale/build/lib && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/DuplicateBB.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
lib/CMakeFiles/DuplicateBB.dir/build: lib/libDuplicateBB.so
.PHONY : lib/CMakeFiles/DuplicateBB.dir/build

lib/CMakeFiles/DuplicateBB.dir/clean:
	cd /home/dalehuang/Documents/llvm-dale/build/lib && $(CMAKE_COMMAND) -P CMakeFiles/DuplicateBB.dir/cmake_clean.cmake
.PHONY : lib/CMakeFiles/DuplicateBB.dir/clean

lib/CMakeFiles/DuplicateBB.dir/depend:
	cd /home/dalehuang/Documents/llvm-dale/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/dalehuang/Documents/llvm-dale /home/dalehuang/Documents/llvm-dale/lib /home/dalehuang/Documents/llvm-dale/build /home/dalehuang/Documents/llvm-dale/build/lib /home/dalehuang/Documents/llvm-dale/build/lib/CMakeFiles/DuplicateBB.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : lib/CMakeFiles/DuplicateBB.dir/depend

