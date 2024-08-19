#ifndef HELPER
#define HELPER

#include <stdlib.h>
#include <stdint.h>
#include <iostream>
#include <functional>
#include <type_traits>
#include <string>
#include <tuple>
#include <array>
#include "monad.h"

/// @brief Returns true if the type param T is an `IOMonad`, and false otherwise 
/// @tparam T The type param to check
template <typename T>
struct is_monad : std::false_type {};

/// @brief Returns true if the type param T is an `IOMonad`, and false otherwise 
/// @tparam T The type param to check
template <typename T>
struct is_monad<IOMonad<T>> : std::true_type {};

/// @brief If the type of the passed parameter is a monad, bind the monad, thereby running its 
/// contents, otherwise just execute the non-monadic function.
/// @tparam F The type of the parameter to be passed
/// @param f The monad or function to be executed
template <typename F>
void bind_if_monad(F&& f) {
    using ReturnType = decltype(f());
    if constexpr (is_monad<ReturnType>::value) {
        f().bind();
    } else {
        f();
    }
}

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
