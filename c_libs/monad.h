#ifndef MONAD
#define MONAD

#include <functional>
#include <type_traits>


/**
 * @brief Fallback when the second template parameter is not a function type.
 * 
 * Static_assert will trigger a compile-time error if instantiated with an invalid second 
 * template parameter.
 */
template<typename, typename T>
struct is_monad {
    static_assert(
        std::integral_constant<T, false>::value,
        "Second template parameter needs to be of function type."
    );
};


/**
 * @brief Specialization of `is_monad` for cases where the second template parameter is a function 
 * type. 
 * 
 * Will actually perform checks to see if a given class `C` has a method that can be called
 * with the specified arguments and return the correct return type.
 * 
 * @tparam C The class to check if it is a monad
 * @tparam Ret The return type we want from the function we are checking for
 */
template<typename C, typename Ret>
struct is_monad<C, Ret()> {
private:
    /**
     * @brief Helper function to check whether class `C` has a method `isMonad` that returns `Ret`.
     * 
     * @tparam T The class to check if it is a monad
     * @return True if T has a method bool isMonad(), otherwise false 
     */
    template<typename T>
    static constexpr auto check(T*)
        -> typename std::is_same<decltype(std::declval<T>().isMonad()), Ret>::type;

    // Fallback template for when the previous template fails because `T` does not have the
    // `isMonad` method with the specified signature.
    template<typename>
    static constexpr std::false_type check(...);

    // Using the result of the `check` function to define the `type`.
    typedef decltype(check<C>(0)) type;

public:
    // Public boolean constant that indicates whether class `C` has an `isMonad` method.
    static constexpr bool value = type::value;
};



/**
 * @brief This class represents a monad, which is used to sequence operations in a defined and rigid
 * way which is not affected by automatic concurrency.
 *  
 * A monad is a monoid in the category of endofunctors, meaning that they are a wrapper around a
 * value which provide the following operations:
 *  - lift: lifts a value into a monad wrapper
 *  - bind: takes a nested monad M(M(x)) and returns a non-nested monad M(x)
 *  - endofunctor: an operation M : C -> C
 * 
 * @tparam T The type of the value contained by the monad
 */
template <typename T>
class Monad {
public:
    /**
     * @brief Construct a new Monad object
     * 
     * @param obj The value contained by the monad
     */
    Monad(T obj) : object(obj) {}

    /**
     * @brief Composes a monadic value with a function arrow a: T -> T to create a new value
     * 
     * This function must be an endofunctor to meet the definition of a monad (i.e. map a category
     * from itself to itself).
     * 
     * @param right The arrow from the old value to the new value
     * @return Monad<T> A monad containing the result of the arrow applied to the value of this 
     * monad
     */
    Monad<T> arrow(Monad<std::function<T(T)>> right) {
        return Monad<T>(right.getObject()(this->object));
    }
    
    /**
     * @brief A natural transformation b: M(M(x)) -> M(x) which flattens a nested monad into a non-
     * nested monad.
     * 
     * @param m The monad to flatten
     * @return Monad<T> The flattened monad
     */
    Monad<T> bind(Monad<Monad<T>> m) { 
        return m.getObject();
    }

    /**
     * @brief Get the value contained within the monad
     * 
     * @return T the value within the monad
     */
    T getObject() {
        return this->object;
    }


    bool isMonad() { return true; }

    /**
     * @brief The value contained within the monadic context 
     */
    const T object;
};


/**
 * @brief Used to represent IO actions in a monadic way to ensure that they happen in a defined, 
 * sequential order which is not affected by automatic concurrency.
 * 
 * @tparam T The value contained within the monadic context.
 */
template <typename T>
class IO : public Monad<T> {
public:
    /**
     * @brief Construct a new IO object
     * 
     * @param obj The value to contain within the IO monadic context
     */
    IO(T obj) : Monad<T>(obj) {}

    virtual IO<T> arrow(Monad<std::function<T(T)>> right) {
        auto l = this->getObject();
        auto r = right.getObject();
        std::function<T()> inner = [l, r] () {
            return r(l);
        };

        return IO<T>(inner());
    }

    /**
     * @brief Composes the value contained by the IO monad (which is a function) with the contained 
     * by the monad passed (which is also a function).
     * 
     * @param right The monad to compose with this monad such that right(this)
     * @return Monad<T> The monad representing the composition of the 2 previous monads
     */
    virtual IO<T> arrow(Monad<T> right) {
        auto l = this->getObject();
        auto r = right.getObject();
        T inner = [l, r] () {
            l();
            r();
        };

        return IO<T>(inner);
    }
};


#endif
