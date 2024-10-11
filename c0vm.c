/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2023                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

#include "lib/xalloc.h"
#include "lib/stack.h"
#include "lib/contracts.h"
#include "lib/c0v_stack.h"
#include "lib/c0vm.h"
#include "lib/c0vm_c0ffi.h"
#include "lib/c0vm_abort.h"

/* call stack frames */
typedef struct frame_info frame;
struct frame_info {
  c0v_stack_t  S;   /* Operand stack of C0 values */
  ubyte       *P;   /* Function body */
  size_t       pc;  /* Program counter */
  c0_value    *V;   /* The local variables */
};

void push_int(c0v_stack_t S, int x)
{
  c0v_push(S, int2val(x));
  return;
}

void push_ptr(c0v_stack_t S, void *a)
{
  c0v_push(S, ptr2val(a));
  return;
}

int pop_int(c0v_stack_t S)
{
  return val2int(c0v_pop(S));
}

void *pop_ptr(c0v_stack_t S)
{
  return val2ptr(c0v_pop(S));
}

int execute(struct bc0_file *bc0) {
  REQUIRES(bc0 != NULL);

  /* Variables */
  c0v_stack_t S; /* Operand stack of C0 values */
  ubyte *P;      /* Array of bytes that make up the current function */
  size_t pc;     /* Current location within the current byte array P */
  c0_value *V;   /* Local variables (you won't need this till Task 2) */
  (void) V;      // silences compilation errors about V being currently unused

  S = c0v_stack_new();
  P = bc0->function_pool[0].code;
  pc = 0;
  V = xmalloc(sizeof(c0_value) * bc0->function_pool[0].num_vars);

  /* The call stack, a generic stack that should contain pointers to frames */
  /* You won't need this until you implement functions. */
  gstack_t callStack;
  // (void) callStack; // silences compilation errors about callStack being currently unused
  callStack = stack_new();

  while (true) {

#ifdef DEBUG
    /* You can add extra debugging information here */
    fprintf(stderr, "Opcode %x -- Stack size: %zu -- PC: %zu\n",
            P[pc], c0v_stack_size(S), pc);
#endif

    switch (P[pc]) {

    /* Additional stack operation: */

    case POP: {
      pc++;
      c0v_pop(S);
      break;
    }

    case DUP: {
      pc++;
      c0_value v = c0v_pop(S);
      c0v_push(S,v);
      c0v_push(S,v);
      break;
    }

    case SWAP: {
      pc++;
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      c0v_push(S,v2);
      c0v_push(S,v1);
      break;
    }

    /* Returning from a function.
     * This currently has a memory leak! You will need to make a slight
     * change for the initial tasks to avoid leaking memory.  You will
     * need to revise it further when you write INVOKESTATIC. */

    case RETURN: {
      // Pop the only value from operand stack (result)
      c0_value retval = c0v_pop(S);
      ASSERT(c0v_stack_empty(S));
// Another way to print only in DEBUG mode
IF_DEBUG(fprintf(stderr, "Returning %d from execute()\n", val2int(retval)));
      // Free everything before returning from the execute function!
      free(V);
      c0v_stack_free(S);

      // Check callstack
      if (stack_empty(callStack)) // No other function needs to be called
      {
        stack_free(callStack, NULL);
        return val2int(retval);
      }
      else // Go back to the interrupted function
      {
        frame* original_state = pop(callStack);
        S = original_state -> S;
        P = original_state -> P;
        pc = original_state -> pc;
        V = original_state -> V;
        free(original_state);
        c0v_push(S, retval); // Push the result into the original operand stack
        break;
      }
    }

    /* Arithmetic and Logical operations */

    case IADD: {
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      int res = x + y;
      push_int(S, res);
      break;
    }

    case ISUB: {
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      int res = x - y;
      push_int(S, res);
      break;
    }

    case IMUL: {
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      int res = x * y;
      push_int(S, res);
      break;
    }

    case IDIV: {
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      if (y == 0) c0_arith_error("Division by zero");
      else if (x == INT_MIN && y == -1) c0_arith_error("Divide int_min by -1");
      else {
        int res = x / y;
        push_int(S, res);
      }
      break;
    }

    case IREM: {
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      if (y == 0) c0_arith_error("Division by zero");
      else if (x == INT_MIN && y == -1) c0_arith_error("Divide int_min by -1");
      else {
        int res = x % y;
        push_int(S, res);
      }
      break;
    }

    case IAND: {
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      int res = x & y;
      push_int(S, res);
      break;
    }

    case IOR: {
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      int res = x | y;
      push_int(S, res);
      break;
    }

    case IXOR: {
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      int res = x ^ y;
      push_int(S, res);
      break;
    }

    case ISHR: {
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      if (y < 0) c0_arith_error("Shift negative bits");
      else if (y >= 32) c0_arith_error("Shift more than 32 bits");
      else {
        int res = x >> y;
        push_int(S, res);
      }
      break;
    }

    case ISHL: {
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      if (y < 0) c0_arith_error("Shift negative bits");
      else if (y >= 32) c0_arith_error("Shift more than 32 bits");
      else {
        int res = x << y;
        push_int(S, res);
      }
      break;
    }

    /* Pushing constants */

    case BIPUSH: {
      pc++;
      int x = (int)(int8_t)P[pc];
      push_int(S, x);
      pc++;
      break;
    }

    case ILDC: {
      pc++;
      uint32_t c1 = (uint32_t)(P[pc]);
      pc++;
      uint32_t c2 = (uint32_t)(P[pc]);
      pc++;
      uint32_t index = (c1 << 8) | c2;
      if (index > (uint32_t)(bc0->int_count)) {
        c0_arith_error("index larger than int count");
      }
      int x = bc0->int_pool[index];
      push_int(S, x);
      break;
    }

    case ALDC: {
      pc++;
      uint32_t c1 = (uint32_t)(P[pc]);
      pc++;
      uint32_t c2 = (uint32_t)(P[pc]);
      pc++;
      uint32_t index = (c1 << 8) | c2;
      if (index > (uint32_t)(bc0->string_count)) {
        c0_arith_error("index larger than string count");
      }
      void *a = (void*)(&bc0->string_pool[index]);
      push_ptr(S, a);
      break;
    }

    case ACONST_NULL: {
      pc++;
      push_ptr(S, NULL);
      break;
    }

    /* Operations on local variables */

    case VLOAD: {
      pc++;
      c0_value v = V[P[pc]];
      c0v_push(S, v);
      pc++;
      break;
    }

    case VSTORE: {
      pc++;
      c0_value v = c0v_pop(S);
      V[P[pc]] = v;
      pc++;
      break;
    }

    /* Assertions and errors */

    case ATHROW: {
      pc++;
      void *a = pop_ptr(S);
      c0_user_error(a);
      break;
    }

    case ASSERT: {
      pc++;
      void *a = pop_ptr(S);
      int x = pop_int(S);
      if (x == 0) c0_assertion_failure(a);
      break;
    }

    /* Control flow operations */

    case NOP: {
      pc++;
      break;
    }

    case IF_CMPEQ: {
      pc++;
      uint16_t o1 = (uint16_t)P[pc];
      pc++;
      uint16_t o2 = (uint16_t)P[pc];
      pc++;
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      if (val_equal(v1, v2)) {
        int16_t index = (int16_t)(o1 << 8 | o2);
        pc = pc + index - 3;
      }
      break;
    }

    case IF_CMPNE: {
      pc++;
      uint16_t o1 = (uint16_t)P[pc];
      pc++;
      uint16_t o2 = (uint16_t)P[pc];
      pc++;
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      if (!val_equal(v1, v2)) {
        int16_t index = (int16_t)(o1 << 8 | o2);
        pc = pc + index - 3;
      }
      break;
    }

    case IF_ICMPLT: {
      pc++;
      uint16_t o1 = (uint16_t)P[pc];
      pc++;
      uint16_t o2 = (uint16_t)P[pc];
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      if (x < y) {
        int16_t index = (int16_t)(o1 << 8 | o2);
        pc = pc + index - 3;
      }
      break;
    }

    case IF_ICMPGE: {
      pc++;
      uint16_t o1 = (uint16_t)P[pc];
      pc++;
      uint16_t o2 = (uint16_t)P[pc];
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      if (x >= y) {
        int16_t index = (int16_t)(o1 << 8 | o2);
        pc = pc + index - 3;
      }
      break;
    }

    case IF_ICMPGT: {
      pc++;
      uint16_t o1 = (uint16_t)P[pc];
      pc++;
      uint16_t o2 = (uint16_t)P[pc];
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      if (x > y) {
        int16_t index = (int16_t)(o1 << 8 | o2);
        pc = pc + index - 3;
      }
      break;
    }

    case IF_ICMPLE: {
      pc++;
      uint16_t o1 = (uint16_t)P[pc];
      pc++;
      uint16_t o2 = (uint16_t)P[pc];
      pc++;
      int y = pop_int(S);
      int x = pop_int(S);
      if (x <= y) {
        int16_t index = (int16_t)(o1 << 8 | o2);
        pc = pc + index - 3;
      }
      break;
    }

    case GOTO: {
      pc++;
      uint16_t o1 = (uint16_t)P[pc];
      pc++;
      uint16_t o2 = (uint16_t)P[pc];
      pc++;
      int16_t index = (int16_t)(o1 << 8 | o2);
      pc = pc + index - 3;
      break;
    }

    /* Function call operations: */

    case INVOKESTATIC: {
      // Get function from function pool
      pc++;
      uint16_t c1 = (uint16_t)(P[pc]);
      pc++;
      uint16_t c2 = (uint16_t)(P[pc]);
      pc++;
      uint16_t index = (c1 << 8 | c2);
      struct function_info *func = &(bc0->function_pool[index]);
      
      // Preserve current state
      frame* state = xmalloc(sizeof(frame));
      state->S = S;
      state->P = P;
      state->pc = pc;
      state->V = V;
      push(callStack, (void*)state);

      // Initialize S, P, pc, V
      int num_vars = (int)(func->num_vars);
      int num_args = (int)(func->num_args);
      V = xmalloc(sizeof(c0_value) * num_vars);
      for (int n = num_args-1; n >= 0; n--) {
        V[n] = c0v_pop(S);
      }

      S = c0v_stack_new();
      P = func->code;
      pc = 0;

      break;
    }

    case INVOKENATIVE: {
      // Get native function from native pool
      pc++;
      uint16_t c1 = (uint16_t)(P[pc]);
      pc++;
      uint16_t c2 = (uint16_t)(P[pc]);
      pc++;
      uint16_t index = (c1 << 8 | c2);
      struct native_info *native = &(bc0->native_pool[index]);

      // Get native function fields
      int num_args = (int)(native->num_args);
      uint16_t native_index = native->function_table_index;
      
      // Populate arguments array
      c0_value *arg_arr = xmalloc(num_args * sizeof(c0_value));
      for (int n=0; n < num_args; n++) {
        int arg_index = num_args - n - 1;
        arg_arr[arg_index] = c0v_pop(S);
      }

      // Pass args into native function, get ressult
      c0_value result = (*native_function_table[native_index])(arg_arr);

      // Push result back to original S
      c0v_push(S, result);
      free(arg_arr);
      break;
    }

    /* Memory allocation and access operations: */

    // Basic Allocation
    case NEW: {
      pc++;
      // int s = (int)(int8_t)P[pc];
      // byte s = P[pc];
      uint8_t s = (uint8_t)P[pc];
      // void *a = (void*)xmalloc(sizeof(s));
      void *a = (void*)xcalloc(s, sizeof(uint8_t));
      push_ptr(S, a);
      pc++;
      break;
    }

    // Accessing memory
    // for integers:
    case IMLOAD: {
      pc++;
      int *a = (int*)pop_ptr(S);
      if (a == NULL) c0_memory_error("NULL pointer");
      int x = *a;
      push_int(S, x);
      break;
    }

    case IMSTORE: {
      pc++;
      int x = pop_int(S);
      int *a = (int*)pop_ptr(S);
      if (a == NULL) c0_memory_error("NULL pointer");
      *a = x;
      break;
    }

    // for pointers:
    case AMLOAD: {
      pc++;
      void **a = pop_ptr(S);
      if (a == NULL) c0_memory_error("NULL pointer");
      void *b = *a;
      push_ptr(S, b);
      break;
    }

    case AMSTORE: {
      pc++;
      void *b = pop_ptr(S);
      void **a = pop_ptr(S);
      if (a == NULL || b == NULL) c0_memory_error("NULL pointer");
      *a = b;
      break;
    }

    // for characters:
    case CMLOAD: {
      pc++;
      char *a = (char*)pop_ptr(S);
      if (a == NULL) c0_memory_error("NULL pointer");
      int x = (int)(int32_t)(*a);
      push_int(S, x);
      break;
    }

    case CMSTORE: {
      pc++;
      int x = pop_int(S);
      char *a = (char*)pop_ptr(S);
      if (a == NULL) c0_memory_error("NULL pointer");
      *a = (x & 0x7F);
      break;
    }

    case AADDF: {
      pc++;
      ubyte f = (ubyte)P[pc];
      pc++;
      char *a = (char*)pop_ptr(S);
      if (a == NULL) c0_memory_error("NULL pointer");
      push_ptr(S, (void*)(a+f));
      break;
    }

    /* Array operations: */

    case NEWARRAY: {
      pc++;
      c0_array *arr = xmalloc(sizeof(c0_array));
      int n = pop_int(S); // count: number of elems
      if (n < 0) c0_memory_error("Negative count");
      int elt_size = (int)P[pc]; // elt_size: number of bytes in a single elem
      pc++;

      // Initialize array field count
      arr->count = n;

      // Initialize array field elt_size
      arr->elt_size = elt_size;

      // Initialize array field elems
      // void *a = (void*)xcalloc(n, sizeof(void*));
      // if (a == NULL) c0_memory_error("NULL pointer");
      arr->elems = xcalloc(n*elt_size, sizeof(byte));
      push_ptr(S, (void*)arr);
      break;
    }

    case ARRAYLENGTH: {
      pc++;
      c0_array* a = (c0_array*) pop_ptr(S);
      if (a == NULL) c0_memory_error("NULL pointer");
      push_int(S, a->count);
      break;
    }

    case AADDS: {
      pc++;
      int i = pop_int(S);
      c0_array* a = (c0_array*) pop_ptr(S);
      if (a == NULL) c0_memory_error("NULL pointer");
      if (i >= (int)a->count) c0_memory_error("Invalid index larger");
      if (i < 0) c0_memory_error("Invalid index negative");
      char *elems = (char*)a->elems;
      void *res = (elems + (a->elt_size) * i);
      push_ptr(S, res);
      break;
    }

    /* BONUS -- C1 operations */

    case CHECKTAG: {
      pc++;
      uint16_t c1 = (uint16_t)P[pc];
      pc++;
      uint16_t c2 = (uint16_t)P[pc];
      pc++;
      uint16_t tag = (uint16_t)(c1 << 8 | c2);

      c0_value a_c0v = c0v_pop(S);
      c0_tagged_ptr *a = val2tagged_ptr(a_c0v);
      uint16_t a_tag = a->tag;

      if (a != NULL && tag == a_tag)
      {
        push_ptr(S, a->p);
      }
      else 
      {
        c0_memory_error("Not correct tag");
      }
      break;
    }

    case HASTAG: {
      pc++;
      uint16_t c1 = (uint16_t)P[pc];
      pc++;
      uint16_t c2 = (uint16_t)P[pc];
      pc++;
      uint16_t tag = (uint16_t)(c1 << 8 | c2);

      c0_value a_c0v = c0v_pop(S);
      c0_tagged_ptr *a = val2tagged_ptr(a_c0v);
      if (a == NULL) c0_memory_error("NULL pointer");
      uint16_t a_tag = a->tag;

      if (a != NULL && tag != a_tag)
      {
        push_int(S, 0);
      }
      else 
      {
        push_int(S, 1);
      }
      break;
    }

    case ADDTAG: {
      pc++;
      uint16_t c1 = (uint16_t)P[pc];
      pc++;
      uint16_t c2 = (uint16_t)P[pc];
      pc++;
      uint16_t tag = (uint16_t)(c1 << 8 | c2);

      void *a = pop_ptr(S);

      c0v_push(S, tagged_ptr2val(a, tag));
      break;
    }

    case ADDROF_STATIC: {
      pc++;
      uint16_t c1 = (uint16_t)P[pc];
      pc++;
      uint16_t c2 = (uint16_t)P[pc];
      pc++;
      uint16_t index = (uint16_t)(c1 << 8 | c2);
      push_ptr(S, &(bc0->function_pool[index].code));
      break;
    }

    case ADDROF_NATIVE: {
      pc++;
      uint16_t c1 = (uint16_t)P[pc];
      pc++;
      uint16_t c2 = (uint16_t)P[pc];
      pc++;
      uint16_t index = (uint16_t)(c1 << 8 | c2);
      
      push_ptr(S, &(native_function_table[(bc0->native_pool[index]).function_table_index]));
      break;
    }

    case INVOKEDYNAMIC:
    {
      void *a = val2ptr(c0v_pop(S));

      // if (a == NULL || !is_funptr(a)) {
      //     c0_memory_error("Invalid function pointer for dynamic invocation");
      //   }

      uint16_t index = funptr2index(a);
      if (is_native_funptr(a)) {

        struct native_info *native = &(bc0->native_pool[index]);

        // Get native function fields
        int num_args = (int)(native->num_args);
        uint16_t native_index = native->function_table_index;
        
        // Populate arguments array
        c0_value *arg_arr = xmalloc(num_args * sizeof(c0_value));
        for (int n=0; n < num_args; n++) {
          int arg_index = num_args - n - 1;
          arg_arr[arg_index] = c0v_pop(S);
          c0_value result = (*native_function_table[native_index])(arg_arr);
          free(arg_arr);
          c0v_push(S, result);
        }
      } 
      else 
      {
        struct function_info *func = &(bc0->function_pool[index]);
      
        // Preserve current state
        frame* state = xmalloc(sizeof(frame));
        state->S = S;
        state->P = P;
        state->pc = pc;
        state->V = V;
        push(callStack, (void*)state);

        // Initialize S, P, pc, V
        int num_vars = (int)(func->num_vars);
        int num_args = (int)(func->num_args);
        V = xmalloc(sizeof(c0_value) * num_vars);
        for (int n = num_args-1; n >= 0; n--) {
          V[n] = c0v_pop(S);
        }

        S = c0v_stack_new();
        P = func->code;
        pc = 0;
        }

      break;
    }

    default:
      fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
      abort();
    }
  }

  /* cannot get here from infinite loop */
  assert(false);
}
