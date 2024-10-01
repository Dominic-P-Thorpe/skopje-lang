#ifndef HELPER
#define HELPER

#include <stdlib.h>
#include <stdint.h>
#include <iostream>
#include <functional>
#include <type_traits>
#include <span>
#include <string>
#include <tuple>
#include <array>
#include <ranges>
#include <utility>
#include <cstdint>
#include <experimental/array>
#include <algorithm>
#include <concepts>

#include "monad.h"
#include "autoparallel.h"


/// @brief If the return type of the passed function is a monad, bind the monad, running its 
/// contents, otherwise just execute the non-monadic function.
/// @tparam F The type of the function to be executed
/// @param f The monad or function to be executed
template <typename F>
void bind_if_monad(F&& f) {
    using ReturnType = decltype(f()); // get the return type of the function
    if constexpr (is_monad<ReturnType, bool()>::value) { // check if the return type is a monad
        // if the value wrapped in the monad is a function, run it, otherwise just return the value
        if constexpr (std::is_invocable_v<decltype(f().getObject())>) {
            f().getObject()();
        } else {
            f().getObject();
        }
    } else { // return type is not a monad, so just run the function
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

    std::array<T, N> arr = { static_cast<T>(std::forward<U>(values))... };
    return arr;
}


/// @brief Creates a struct of type T using the first I elements from the passed tuple.
/// @tparam T The type of the struct to create.
/// @tparam Tuple A tuple containing the arguments to create the struct from.
/// @tparam Is A parameter pack of indices representing the elements in the tuple to use.
/// @param tuple The tuple containing the arguments for struct construction.
/// @param index_sequence A sequence of indices corresponding to the tuple elements to use.
/// @return An instance of T created with the specified tuple elements.
template <typename T, typename Tuple, std::size_t... Is>
constexpr T create_struct_impl(Tuple&& tuple, std::index_sequence<Is...>) {
    return T{std::get<Is>(std::forward<Tuple>(tuple))...};
}


/// @brief Creates an instance of T by passing the first N arguments from the variadic template 
/// arguments.
/// @tparam T The type of the struct to create.
/// @tparam N The number of arguments to use for constructing T.
/// @tparam Args The types of the variadic arguments passed to the function.
/// @param args The arguments to use for constructing the struct of type T.
/// @return An instance of T created using the first N arguments from args.
template <typename T, std::size_t N, typename... Args>
constexpr T create_struct(Args&&... args) {
    if constexpr (sizeof...(Args) < N) {
        return T{};
    } else {
        // Create a tuple of the arguments
        auto args_tuple = std::make_tuple(std::forward<Args>(args)...);
        // Create a sequence of the first num_required indices
        return create_struct_impl<T>(args_tuple, std::make_index_sequence<N>{});
    }
}


/// Requires that the given type parameter be an instance of std::array
template<typename T>
concept IsStdArray = requires(T) {
    typename std::tuple_size<T>::type;
    requires std::is_same_v<T, std::array<typename T::value_type, std::tuple_size_v<T>>>;
};


/// @brief Gets the last elements of an std::array instance starting at the given index
/// @tparam T The type of the array, such as std::array<uint_32, 20>
/// @tparam Start The index of the first element to get from the original array
/// @param arr The array to get the last elements of
/// @return An array of the last elements of the original array starting from the element at the 
/// given starting index
template <IsStdArray T, std::size_t Start>
constexpr auto get_last_elements(const T& arr) {
    // calculate the size of the new array
    constexpr std::size_t N = std::tuple_size_v<T>;

    // the new array to store the final elements in
    constexpr auto subarray_size = N - Start;
    std::array<typename T::value_type, subarray_size> result{};
    
    // copy the final elements of the old array into the new array
    std::ranges::copy(arr | std::views::drop(Start), result.begin());
    
    return result;
}


/// @brief An alias for std::to_string which converts a float to a string
/// @param f The float to stringify
/// @return The float as a string
std::string float2str(float f) {
    return std::to_string(f);
}


/// @brief An alias for std::to_string which converts an integer to a string
/// @param i The integer to stringify
/// @return The integer as a string
std::string int2str(int64_t i) {
    return std::to_string(i);
}


/// @brief An alias for std::to_string which converts a boolean to a string
/// @param b The boolean to stringify
/// @return The boolean as a string
std::string bool2str(bool b) {
    return b ? "true" : "false";
}


uint64_t logical_right(uint64_t target, unsigned int bits) {
    return target >> bits;
}


int64_t arith_right(uint64_t target, unsigned int bits) {
    return target >> bits;
}

#endif
