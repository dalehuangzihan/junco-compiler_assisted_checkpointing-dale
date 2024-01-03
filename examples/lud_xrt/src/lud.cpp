#include "lud.h"
#include <pthread.h>
#ifndef FPGA_TARGET
#include <unistd.h>
#endif

#include <iostream>
#include <fstream>
#include <string.h>

extern "C"
{

  static unsigned int heartbeat = 0;

  char sync_bit = 0;
  int call_cpt = 0;

  void cpy_wrapper_f(dataType *dest, dataType *src, int size)
  {
    memcpy(dest, src, size);
    sync_bit = 1;
  }

  void cpy_wrapper_i8(unsigned char *dest, unsigned char *src, int size)
  {
    memcpy(dest, src, size);
    sync_bit = 1;
  }

  /*
  void  __attribute__ ((noinline)) push_stack(int* stack_ptr, int* sp, int value){
    if(stack_ptr == NULL){
      printf("NULL stack ptr \n");
      return;
    }

    printf("stack[%d]=%d (%p)\n", *sp, value, stack_ptr);
    stack_ptr[*sp] = value;
  }
  */
  void __attribute__((noinline)) mem_cpy_index_f(dataType *dest, dataType *src, int *index_list, int *sp)
  {
    if (dest == NULL)
      return;

    /*
    if((call_cpt%2) == 0)
      dest[2] = *sp;
    else
      dest[1] = *sp;
    call_cpt++;

    int i=0;
    */
    while (*sp > 0)
    {
      (*sp)--;
      int index = index_list[*sp];
      dest[index] = src[index];
      // dest[i] = index; //src[index];
      // i++;
    }

    /*
    for(i=10; i<20; i++){
      dest[i] = i;
    }
    */
    sync_bit = 1;
  }

  void checkpoint()
  {
    mem_cpy_index_f(NULL, NULL, NULL, NULL);
    cpy_wrapper_f(NULL, NULL, 0);
    cpy_wrapper_i8(NULL, NULL, 0);
  }

  /*#FUNCTION_DEF#*/
  /* FUNC lud : ARGS result{}[262144], size{}[] */
  void lud(double *result, int size, double *ckpt_mem, int ckpt_id)
  {
    int i, j, k;
    double sum;
    int init_i = 0;

    printf(">> lud: run from process PID = %d (ckpt id %d) %p\n>> ", getpid(), ckpt_id, ckpt_mem);

    for (i = init_i; i < size; i++)
    {

      for (j = i; j < size; j++)
      {
        sum = result[i * size + j];
        for (k = 0; k < i; k++)
          sum -= result[i * size + k] * result[k * size + j];
        result[i * size + j] = sum;
        // checkpoint(); // lvl 2 ckpt
      }
      // checkpoint(); // lvl 1 ckpt

      for (j = i + 1; j < size; j++)
      {
        sum = result[j * size + i];
        for (k = 0; k < i; k++)
          sum -= result[j * size + k] * result[k * size + i];
        result[j * size + i] = sum / result[i * size + i];
        // checkpoint(); // lvl 2 ckpt
      }

      if (i % 1 == 0)
      {
        checkpoint(); // lvl 1 ckpt
      }
      // checkpoint(); // lvl 1 ckpt
      printf("%d ", i);
    }
    printf(">> lud: after checkpoint");

    return;
  }

  /*#FUNCTION_DEF#*/
  /* FUNC workload : ARGS result{}[262144], size{const}[] */
  int workload(double *result, int size, double *ckpt_mem, int initial)
  {
    printf("> workload: Starting workload\n");

    int ckpt_id = ckpt_mem[CKPT_ID];
    lud(result, size, ckpt_mem, ckpt_id);
    ckpt_mem[COMPLETED] = ((initial == 1) ? 0 : 1);

    printf("> workload: isComplete=%f\n", ckpt_mem[COMPLETED]);
    return (int)ckpt_mem[COMPLETED];
  }
}
