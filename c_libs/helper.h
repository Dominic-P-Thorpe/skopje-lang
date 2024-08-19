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
#include <experimental/array>
#include <algorithm>
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


/// @brief Takes 2 arrays as arguments and concatenates them, returning arr2 appended to arr1.
/// @tparam T The type of the elements of arr1 and arr2
/// @tparam N The size of arr1
/// @tparam M The size of arr2
/// @param arr1 The array at the start of the new array
/// @param arr2 The array at the end of the new array
/// @return Arr2 concatenated to the end of arr1
template <typename T, std::size_t N, std::size_t M>
std::array<T, N + M> concatenate(const std::array<T, N>& arr1, const std::array<T, M>& arr2) {
    std::array<T, N + M> result;

    // Copy elements from the first array
    std::copy(arr1.begin(), arr1.end(), result.begin());

    // Copy elements from the second array
    std::copy(arr2.begin(), arr2.end(), result.begin() + N);

    return result;
}


#endif
