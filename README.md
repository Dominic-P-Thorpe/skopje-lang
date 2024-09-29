# The Skopje Programming Language

The Skopje programming language is an exciting new programming language currently under heavy development designed for automatic parallelism. It draws heavy inspiration from Rust, Haskell, Clean, and seeks to combine automatic parallelism with the best of functional programming without sacrificing the convenience of imperative programming.

The project is written in Rust, and the compiler compiles down to C++. This project also contains the essential libraries required for the produced C++ source code to compile. Note that the compiler compiles to C++ 20 and the relevant version of GCC/G++ must be installed.

The compiler is currently working on stabilising version 0.1.0 (proof-of-concept) and designing version 0.1.1 (structs).

## Installation and Getting Started

To get started, follow these steps:
1) Clone the repository into a directory of your choice,
2) Navigate into the directory and build the project using `cargo build --release`,
3) Navigate into `skopje/target/release/` where the compiler executable will be located,
4) Run the exe using:
   1) Windows: `./skopje -- <input filename> <C++ output filename>`
5) Compile the resulting C++ intermediate file with `g++ <C++ output filename> -o <executable filename -std=c++20`.
   1) If you have problems compiling the C++ file with C++ 20, try updating G++ 

## Features

What follows is an overview of the *currently implemented* features of the Skopje programming language's compiler. A full specification of the planned language can be found [here](#).

### Basic Syntax

As previously mentioned, the basic syntax and type system of Skopje is heavily inspired by Rust and Haskell. The semantics and type system are constructed to ensure that automatic parallelism can be achieved as much as possible without any special effort from the programmer.

Note that all Skopje programs, like in C, must have a main function with the declaration `fn main() -> i32`, which is the entrypoint to the program.

#### Functions

Functions are declared using the `fn` keyword, followed by the name of the function, a comma-separated list of parameters enclosed in parentheses where each parameter is in the form `<identifier> : <type>`, then an arrow and the return type, and then the body of the function enclosed in curly brackets.

```
fn sum_of_squares(a: i32, b: i32) -> i32 {
    let a_squared: i32 = a * a;
    let b_squared: i32 = b * b;
    return a_squared + b_squared;
}
```

#### Variables

An example of variable declaration can be seen in the example above. It uses the `let` keyword, followed by the identifier of the variable, a colon, the type of the variable, an equals sign, then an expression to assign to the variable.

#### Expressions

Expressions are an essential part of any programming language and are the bedrock of performing calculations. Skopje uses the usual syntax of infix binary operations, plus a few prefix and postfix operations. The operations have the expected precedence and are as follows:
 - +, - (unary prefix and binary infix),
 - *, /, %, &&, ||, ==, !=, >=, <=, >, < (binary infix)
 - \-, !, ~ (unary prefix)
 - \[x\] (array index access, unary postfix)
 - ?: (ternary, as in C)

### Datatypes

The basic datatypes available in Skopje are as follows:
 - signed and unsigned integers 8, 16, 32, and 64 bytes in size (i8, u8, i16, u16, i32, u32, i64, u64 respectively),
 - 32 and 64 bit floating point numbers (f32 and f64)
 - Strings (str)
 - Booleans (bool)

There are also aggregate datatypes available:
 - arrays
 - enumerations (which combine structs and unions)

### Control Flow Structures

## Examples

### Runge-Kutta Numerical Integration

```
fn ode(t: f32, y: f32) -> f32 {
    return y + t;
}

fn runge_kutta_4(y_0: f32, t_0: f32, t_n: f32, h: f32) -> f32 {
    let mut t: f32 = t_0;
    let mut y: f32 = y_0;

    while (t < t_n) {
        // Calculate the four Runge-Kutta increments (k1, k2, k3, k4)
        let k1: f32 = h * ode(t, y);
        let k2: f32 = h * ode(t + h/2, y + k1/2);
        let k3: f32 = h * ode(t + h/2, y + k2/2);
        let k4: f32 = h * ode(t + h, y + k3);

        // Update the value of y using the weighted average of the slopes
        y = y + (1.0/6.0) * (k1 + 2*k2 + 2*k3 + k4);

        // Update the value of t
        t = t + h;
    }

    return y;
}

fn main() -> IO<void> {
    let result: f32 = runge_kutta_4(1, 0, 2, 0.1);
    let result_action: IO<void> = do {
        print(float2str(result));
    };
    
    return result_action;
}
```

## Roadmap

- [ ] Version 0.2.0 (Automatic Parallelism)
  - [x] Version 0.1.2 (Monads)
  - [ ] Version 0.1.3 (Linear Types)
  - [ ] Version 0.1.4 (Automatic Parallelism)
    - [ ] Dependency analysis
    - [ ] Automatic concurrency
  - [ ] Version 0.1.5 (Functional Functions)
    - [ ] Closures?
    - [ ] Anonymous functions
    - [ ] Function-type parameters
- [ ] Version 0.3.X (Polymorphism and Genericity)
  - [ ] Version 0.3.0 (Generics)
  - [ ] Version 0.3.1 (Variadics and Defaults)
  - [ ] Version 0.3.2 (Polymorphic Overloading)
