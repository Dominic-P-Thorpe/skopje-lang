#include "skopje_gc.h"


/// @brief Resize the memory allocated to the given pointer from the old size to the new size. If 
///        the new size is 0, free the memory.
/// @cite Robert Nystrom (2021), Crafting Interpreters - Chunks of Bytecode, 
///       link: https://craftinginterpreters.com/chunks-of-bytecode.html
/// @author Robert Nystrom, Dominic Thorpe
/// @param pointer Pointer to the old block of memory to be reallocated
/// @param old_size Old size of the block of memory (0 if a whole new malloc is required)
/// @param new_size New size of the block of memory (if 0 then free the memory)
/// @return Pointer to the new block of memory, or NULL if it was freed
void* reallocate(void* pointer, uint64_t old_size, uint64_t new_size) {
    if (new_size == 0) {
        free(pointer);
        return NULL;
    }

    void* result = realloc(pointer, new_size);
    return result;
}


/// @brief Creates a new vector with the initial size set to START_VEC_SIZE (from skopje_gc.h)
/// @return A pointer to the new vector
Vector new_vec() {
    Vector vec = {
        START_VEC_SIZE, // max capacity upon creation of new vec
        0, // current size (num elems in vec starts at 0)
        malloc(sizeof(RefCountedObject) * START_VEC_SIZE)
    };

    return vec;
}


/// @brief Wraps the object in a RefCountedObject and inserts it into the end of the vector. Vector
///        is expanded to double its current capacity if full.
/// @param obj_vec The vector to insert the object into
/// @param object The object to insert
/// @return The index of the vector that the new object was inserted into
uint64_t insert_new_object(Vector* obj_vec, void* object) {
    RefCountedObject* rc_obj = malloc(sizeof(RefCountedObject));
    rc_obj->object = object;
    rc_obj->refs = 1;

    // expand the size of the vector if it is full
    if (obj_vec->current_size >= obj_vec->max_capacity) {
        uint64_t old_size = obj_vec->max_capacity;
        obj_vec->max_capacity = obj_vec->max_capacity < START_VEC_SIZE ? START_VEC_SIZE : obj_vec->max_capacity * 2;
        obj_vec->objects = reallocate(obj_vec->objects, old_size, obj_vec->max_capacity);
    }

    // insert the new object into the vector
    obj_vec->objects[obj_vec->current_size] = rc_obj;
    obj_vec->current_size++;

    return obj_vec->current_size - 1;
}


/// @brief Frees the memory used by the object at the given index in the given vector and sets the
///        value there to NULL.
/// @param obj_vec The vector to remove from
/// @param object_index The index of the object to remove
void remove_object(Vector* obj_vec, uint64_t object_index) {
    if (object_index >= obj_vec->max_capacity)
        return;

    free(obj_vec->objects[object_index]->object);
    free(obj_vec->objects[object_index]);
    obj_vec->objects[object_index] = NULL;
}
