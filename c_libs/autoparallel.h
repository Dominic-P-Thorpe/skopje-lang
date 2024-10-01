#include <future>
#include <functional>
#include <thread>
#include <iostream>


/**
 * @brief A wrapper around std::future which adds some convenience features and extra safety when
 * getting to prevent issues with multiple gets.
 * 
 * @tparam T The return type of the function which is to be executed by the future
 * @tparam Args The types of the arguments to be passed to the function to be executed by the future
 * 
 * @todo Integrate with a threadpool?
 * @see https://en.cppreference.com/w/cpp/thread/future
 * 
 * @example
 * ```
 * int main() {
 *     // define the function we are going to put into the future and its arguments
 *     const int32_t a = 1;
 *     const int32_t b = 2;
 *     std::function<int32_t(int32_t, int32_t)> f = [](int32_t a, int32_t b) { return a + b; };
 *     
 *     // create the AutoFuture
 *     AutoFuture<int32_t, int32_t, int32_t> c = AutoFuture<int32_t, int32_t, int32_t>(f, a, b);
 *     
 *     // extract the result and print it to the console
 *     int32_t result = c.get();
 *     std::cout << "Done!\nResults are: " << result << std::endl;
 *     return 0;
 * }
 * ```
 */
template <typename T, typename... Args>
class AutoFuture {
public:
    /**
     * @brief Construct a new Auto Future object
     * 
     * @param func The function to be executed by the future
     * @param args The arguments for the function to be executed by the future
     */
    AutoFuture(std::function<T(Args...)> func, Args... args) {
        this->future = std::async(std::launch::async, func, args...);
    }


    /**
     * @brief Returns the result of executing the future.
     * 
     * Blocks if the future has not yet completed, otherwise returns result immediately.
     * 
     * @return T The return type of the future.
     */
    T get() {
        if (completed) // if the future has already been resolved, return the result immediately
            return result;
        
        // wait for the future to be resolved, get the result, mark the future as complete,
        // and return the result.
        this->future.wait();
        this->result = this->future.get();
        this->completed = true;
        return result;
    }


    /**
     * @brief Implicit type conversion from AutoFuture<T> to T
     * 
     * @return T Value returned by the future wrapped in this AutoFuture
     */
    operator T() {
        return this->get();
    }


private:
    /// @brief The future this AutoFuture wraps around
    std::future<T> future;
    /// @brief True if the future has been resolved and value gotten, otherwise false
    bool completed = false;
    /// @brief The result of the future if it has already been evaluated
    T result;
};
