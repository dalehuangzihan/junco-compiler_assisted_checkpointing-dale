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
include lib/CMakeFiles/BuildMulAddFunc.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include lib/CMakeFiles/BuildMulAddFunc.dir/compiler_depend.make

# Include the progress variables for this target.
include lib/CMakeFiles/BuildMulAddFunc.dir/progress.make

# Include the compile flags for this target's objects.
include lib/CMakeFiles/BuildMulAddFunc.dir/flags.make

lib/CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.o: lib/CMakeFiles/BuildMulAddFunc.dir/flags.make
lib/CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.o: ../lib/BuildMulAddFunc.cpp
lib/CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.o: lib/CMakeFiles/BuildMulAddFunc.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/dalehuang/Documents/llvm-dale/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object lib/CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.o"
	cd /home/dalehuang/Documents/llvm-dale/build/lib && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT lib/CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.o -MF CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.o.d -o CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.o -c /home/dalehuang/Documents/llvm-dale/lib/BuildMulAddFunc.cpp

lib/CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.i"
	cd /home/dalehuang/Documents/llvm-dale/build/lib && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/dalehuang/Documents/llvm-dale/lib/BuildMulAddFunc.cpp > CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.i

lib/CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.s"
	cd /home/dalehuang/Documents/llvm-dale/build/lib && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/dalehuang/Documents/llvm-dale/lib/BuildMulAddFunc.cpp -o CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.s

# Object files for target BuildMulAddFunc
BuildMulAddFunc_OBJECTS = \
"CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.o"

# External object files for target BuildMulAddFunc
BuildMulAddFunc_EXTERNAL_OBJECTS =

lib/libBuildMulAddFunc.so: lib/CMakeFiles/BuildMulAddFunc.dir/BuildMulAddFunc.cpp.o
lib/libBuildMulAddFunc.so: lib/CMakeFiles/BuildMulAddFunc.dir/build.make
lib/libBuildMulAddFunc.so: lib/CMakeFiles/BuildMulAddFunc.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/dalehuang/Documents/llvm-dale/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX shared library libBuildMulAddFunc.so"
	cd /home/dalehuang/Documents/llvm-dale/build/lib && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/BuildMulAddFunc.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
lib/CMakeFiles/BuildMulAddFunc.dir/build: lib/libBuildMulAddFunc.so
.PHONY : lib/CMakeFiles/BuildMulAddFunc.dir/build

lib/CMakeFiles/BuildMulAddFunc.dir/clean:
	cd /home/dalehuang/Documents/llvm-dale/build/lib && $(CMAKE_COMMAND) -P CMakeFiles/BuildMulAddFunc.dir/cmake_clean.cmake
.PHONY : lib/CMakeFiles/BuildMulAddFunc.dir/clean

lib/CMakeFiles/BuildMulAddFunc.dir/depend:
	cd /home/dalehuang/Documents/llvm-dale/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/dalehuang/Documents/llvm-dale /home/dalehuang/Documents/llvm-dale/lib /home/dalehuang/Documents/llvm-dale/build /home/dalehuang/Documents/llvm-dale/build/lib /home/dalehuang/Documents/llvm-dale/build/lib/CMakeFiles/BuildMulAddFunc.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : lib/CMakeFiles/BuildMulAddFunc.dir/depend

