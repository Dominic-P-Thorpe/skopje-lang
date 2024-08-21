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
#include <utility>
#include <cstdint>
#include <experimental/array>
#include <algorithm>
#include <concepts>
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


/// Ensures that the given type parameter is an integer type
template <typename T>
concept Integer = std::is_integral_v<T>;


/// @brief Creates an array of consecutive integers between the start (inclusive) and end 
/// (exclusive) arguments. If the start is greater than the end, then the numbers in the array are
/// reversed. If start == end, then the array is empty. 
/// @tparam T The type of the elements of the array
/// @tparam N The length of the array
/// @param start The number at the start of the range (inclusive)
/// @param end The number at the end of the array (exclusive)
/// @return An ascending array of consecutive numbers if start > end, or descending if start < end,
/// or an empty array if start == end.
template <Integer T, std::size_t N>
std::array<T, N> array_range(int64_t start, int64_t end) {
    std::array<T, N> array;
    if (start == end)
        return {};

    size_t index = 0;
    for (int64_t i = start; i != end; start >= end ? i-- : i++) {
        array[index] = i;
        index++;
    }

    return array;
}


/// @brief Given an array, its size, and a start and end index, return a subarray of that array
/// from the given start index to the given end index.
/// @note Statically asserts that the end index of the subarray is within the bounds of the 
/// original array
/// @tparam T The type of the elements of the new and original array
/// @tparam N The length of the original array
/// @tparam S The start index
/// @tparam E The end index
/// @param original The array to create a subarray from
/// @param start The start index of the subarray (inclusive)
/// @param end The end index of the subarray (exclusive)
/// @return The subarray of the original array within the window [start, end)
template <typename T, std::size_t N, std::size_t S, std::size_t E>
std::array<T, E - S> subarray(std::array<T, N> original, std::size_t start, std::size_t end) {
    // assert that we are not trying to get a subarray from outside the bounds of the original array
    static_assert(E < N); 
    
    // copy from the old array into the new array
    std::array<T, E - S> new_array;
    for (size_t i = start; i < end; i++) {
        // i - start is to make sure that the index of new array is 0 + i and not start + i
        new_array[i - start] = original[i];
    }

    return new_array;
}


/// @brief Creates an array of the given length with elements of the given type.
/// @tparam T The type of the elements of the array
/// @tparam ...U Variadic template for the number of arguments
/// @tparam N The size of the array to be created
/// @param ...values The values to go into the array
/// @return The newly created array
template <typename T, std::size_t N, typename... U>
std::array<T, N> make_array(U&&... values) {
    static_assert(sizeof...(values) == N, "Number of values must match the size of the array.");

    std::array<T, N> arr;
    T temp[] = { static_cast<T>(std::forward<U>(values))... };
    
    for (std::size_t i = 0; i < N; ++i) {
        arr[i] = temp[i];
    }

    return arr;
}

#endif
