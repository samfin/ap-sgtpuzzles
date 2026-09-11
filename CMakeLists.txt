cmake_minimum_required(VERSION 3.5)

project(puzzles
  LANGUAGES C)

set(PUZZLES_ROOT_DIR "${CMAKE_CURRENT_LIST_DIR}")
include(cmake/setup.cmake)

add_library(core_obj OBJECT
  combi.c divvy.c draw-poly.c drawing.c dsf.c findloop.c grid.c
  keen_forced_solver.c
  latin.c laydomino.c loopgen.c malloc.c matching.c midend.c misc.c
  penrose.c penrose-legacy.c ps.c random.c sort.c tdq.c tree234.c
  version.c
  ${platform_common_sources})
add_library(core STATIC $<TARGET_OBJECTS:core_obj>)
add_library(common STATIC $<TARGET_OBJECTS:core_obj> hat.c spectre.c)

cliprogram(polygon-test draw-poly.c
  SDL2_LIB COMPILE_DEFINITIONS STANDALONE_POLYGON)

include_directories(${CMAKE_CURRENT_SOURCE_DIR})

# This is a Keen-only fork of the Simon Tatham Portable Puzzle Collection
# (for the sgtkeen Archipelago apworld) -- every other puzzle type has been
# removed from the build (and deleted from disk) to keep the build fast and
# simple. See ap-sgtpuzzles-web's project notes for context.
puzzle(keen
  DISPLAYNAME "Keen"
  DESCRIPTION "Arithmetic Latin square puzzle"
  OBJECTIVE "Complete the latin square in accordance with the \
arithmetic clues.")
solver(keen latin.c)

add_subdirectory(auxiliary)

if(build_cli_programs)
  write_generated_games_header()
  include(CheckFunctionExists)
  check_function_exists(HF_ITER HAVE_HF_ITER)
  set(WITH_LIBFUZZER OFF
    CACHE BOOL "Build fuzzpuzz using Clang's libFuzzer")
  cliprogram(fuzzpuzz fuzzpuzz.c list.c ${puzzle_sources}
    COMPILE_DEFINITIONS COMBINED $<$<BOOL:${WITH_LIBFUZZER}>:OMIT_MAIN>
    $<$<BOOL:${HAVE_HF_ITER}>:HAVE_HF_ITER>)
  target_include_directories(fuzzpuzz PRIVATE ${generated_include_dir})
  if(WITH_LIBFUZZER)
    target_compile_options(fuzzpuzz PRIVATE -fsanitize=fuzzer)
    set_target_properties(fuzzpuzz PROPERTIES LINK_FLAGS -fsanitize=fuzzer)
  endif()
endif()

build_extras()
