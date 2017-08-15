include_directories(..)

set(VASAN_CFLAGS -ggdb -O2  -U_FORTIFY_SOURCE)

add_custom_target(vasan)
add_custom_target(vasan_backtrace)
add_custom_target(vasan_stats)
add_custom_target(vasan_libc)

add_compiler_rt_runtime(clang_rt.vasan
        STATIC
        ARCHS x86_64 
        SOURCES vasan.cc
        CFLAGS ${VASAN_CFLAGS} -fvisibility=default -DNO_BACKTRACE
        PARENT_TARGET vasan)

add_compiler_rt_runtime(clang_rt.vasan_backtrace
        STATIC
        ARCHS x86_64 
        SOURCES vasan.cc
        CFLAGS ${VASAN_CFLAGS} -fvisibility=default
        PARENT_TARGET vasan_backtrace)

add_compiler_rt_runtime(clang_rt.vasan_stats
        STATIC
        ARCHS x86_64 
        SOURCES vasan.cc
        CFLAGS ${VASAN_CFLAGS} -fvisibility=default -DVASAN_STATISTICS
        PARENT_TARGET vasan_stats)
add_compiler_rt_runtime(clang_rt.vasan_libc
        STATIC
        ARCHS x86_64 
        SOURCES vasan.c
        CFLAGS ${VASAN_CFLAGS} -fvisibility=default
        PARENT_TARGET vasan_libc)


# add_sanitizer_rt_symbols(clang_rt.vasan)
# add_sanitizer_rt_symbols(clang_rt.vasan_backtrace)
# add_sanitizer_rt_symbols(clang_rt.vasan_stats)
# add_sanitizer_rt_symbols(clang_rt.vasan_libc)

# add_dependencies(compiler-rt vasan)
# add_dependencies(compiler-rt vasan_backtrace)
# add_dependencies(compiler-rt vasan_stats)
# add_dependencies(compiler-rt vasan_libc)
