#ifndef SKOPJE_GC
#define SKOPJE_GC

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#define START_VEC_SIZE 8


/// @brief Used to store a pointer to an arbitrary heap object and the number of references to it
typedef struct {
    void* object;
    uint64_t refs;
} RefCountedObject;


/// @brief A dynamically-sized vector data structure for storing reference counted objects
/// @see RefCountedObject
typedef struct {
    uint64_t max_capacity;
    uint64_t current_size;
    RefCountedObject** objects;
} Vector;


void* reallocate(void* pointer, uint64_t old_size, uint64_t new_size);

Vector new_vec();
uint64_t insert_new_object(Vector* obj_vec, void* object);
void remove_object(Vector* obj_vec, uint64_t object_index);

#endif