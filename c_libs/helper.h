#ifndef HELPER
#define HELPER

#include <stdlib.h>
#include <stdint.h>
#include <iostream>
#include <functional>
#include <type_traits>
#include <string>
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

/// @brief Prints the given message and then takes input until the user presses enter
/// @param msg The message to print to standard I/O (no newline added automatically)
/// @return The user's response from standard I/O
std::string readln(std::string msg) {
    std::cout << msg;
    std::string input;
    std::cin >> input;

    return input; 
}

#endif
