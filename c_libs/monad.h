#ifndef MONAD
#define MONAD

#include <vector>
#include <functional>
#include <stdint.h>


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


template <typename T>
IOMonad<T>::IOMonad(T value) : value(value) {}


template <typename T>
IOMonad<T> IOMonad<T>::lift(T value) {
    return IOMonad<T>(value);
}


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


template <typename T>
void IOMonad<T>::add_action(T action) {
    this->action.push_back(action);
}


template <typename T>
IOMonad<T> IOMonad<T>::arrow(T func) {
    IOMonad<T> new_monad = IOMonad<T>(this->value);
    new_monad.add_action(func);
    return new_monad;
}


#endif
