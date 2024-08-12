#ifndef MONAD
#define MONAD

#include <vector>
#include <functional>
#include <stdint.h>


/// @brief Represents the monad for IO actions. IO actions may be composed with the arrow function
/// and created by lifting a regular function to monad status. The monad may be executed by binding
/// it.
/// @tparam T The function represented by the monad (lifted)
template <typename T>
class IOMonad {
    private:
        T value;
        std::vector<T> action;
    
        IOMonad(T value);


    public:
        static IOMonad<T> lift(T value);
        T bind();
        IOMonad<T> arrow(T func);
        void add_action(T action);
};



/// @brief Creates a new monad by lifting the passed value to monad status.
/// @tparam T The type of the value represented by the monad
/// @param value The value the monad shall represent
template <typename T>
IOMonad<T>::IOMonad(T value) : value(value) {}


/// @brief Creates a new monad by lifting the passed value to monad status.
/// @tparam T The type of the value represented by the monad
/// @param value The value the monad shall represent
/// @return The new monad
template <typename T>
IOMonad<T> IOMonad<T>::lift(T value) {
    return IOMonad<T>(value);
}


/// @brief Executes the monad, including the chain of functions which have been added to it with
/// arrows, returning the result.
/// @tparam T The type of the value represented by the monad
/// @return The value after each function applied to it by arrows have been applied
template <typename T>
T IOMonad<T>::bind() {
    if (this->action.size() == 0)
        return this->value;
    
    T intermediate = this->value;
    intermediate();
    for (uint32_t i = 0; i < this->action.size(); i++) {
        intermediate = this->action[i];
        intermediate();
    }
    
    return intermediate;
}


/// @brief Adds a new action to the end of the list of actions represented by the monad
/// @tparam T The type of the value represented by the monad
/// @param action The action to add to the monad
template <typename T>
void IOMonad<T>::add_action(T action) {
    this->action.push_back(action);
}


/// @brief Chains 2 monads together, the left being fed into the right, and returns a new monad
/// representing the combination of the two.
/// @tparam T The type of the value represented by both the old monads and the new monad
/// @param func The monad to be chained onto the end of the current monad
/// @return The new monad representing the result of the arrow operation
template <typename T>
IOMonad<T> IOMonad<T>::arrow(T func) {
    IOMonad<T> new_monad = IOMonad<T>(this->value);
    new_monad.add_action(func);
    return new_monad;
}


#endif
