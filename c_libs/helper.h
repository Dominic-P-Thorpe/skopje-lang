#ifndef HELPER
#define HELPER

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <functional>
#include <type_traits>
#include "monad.h"

/// Executes the return value of the given function if f is of type IOMonad<T>, otherwise just
/// returns the return value 
#define BIND_IF_MONAD(f) if (is_monad<decltype(f())>::value) {f().bind()();} else {f();}

/// @brief Returns true if the type param T is an `IOMonad`, and false otherwise 
/// @tparam T The type param to check
template <typename T>
struct is_monad : std::false_type {};

/// @brief Returns true if the type param T is an `IOMonad`, and false otherwise 
/// @tparam T The type param to check
template <typename T>
struct is_monad<IOMonad<T>> : std::true_type {};

#endif
