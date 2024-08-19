#include <memory>
#include <utility> // for std::forward

template <typename T, typename... Args>
std::unique_ptr<T[]> init_array(Args&&... args) {
    // Size of the array is the number of arguments
    std::size_t size = sizeof...(Args);

    // Allocate memory for the array
    std::unique_ptr<T[]> array(new T[size]);

    // Initialize the array with the arguments using fold expression
    std::size_t index = 0;
    ((array[index++] = std::forward<Args>(args)), ...);

    return array;  // Return the unique_ptr
}

