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
        void arrow(T func);
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
void IOMonad<T>::arrow(T func) {
    this->action.push_back(func);
}


#endif
