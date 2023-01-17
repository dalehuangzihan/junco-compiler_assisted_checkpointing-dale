#include"lud.h"
#include <pthread.h>
#ifndef FPGA_TARGET
#include <unistd.h>
#endif

#include <iostream>
#include <fstream>
#include <string.h>

extern "C"{

  static unsigned int heartbeat = 0;

  void checkpoint(float* ckpt_mem, int i, float* result, int size, int id, char inst) {
    #pragma HLS INLINE OFF
    #pragma HLS FUNCTION_INSTANTIATE variable=inst
    
    ckpt_mem[HEARTBEAT] = heartbeat++;
    ckpt_mem[CKPT_ID] = id;
    ckpt_mem[VAR1] = i;
    for(int ind=0; ind< size*size; ind++){
      ckpt_mem[RESULT+ind] = result[ind];
    }
    
  }
  
  void lud(float* result, int size, float* ckpt_mem, int ckpt_id)
  {
    int i, j, k; 
    float sum;

    //completed[0] = 0;
    ckpt_mem[COMPLETED] = 0;
    
    #ifdef CPU_VERSION
      printf("lud run from process PID = %d (ckpt id %d) %p\n", getpid(), ckpt_id, ckpt_mem);
    #endif

    int init_i = 0;
    if(ckpt_id ==  1){
      init_i = std::round(ckpt_mem[VAR1])+1;
      for (int ind=0; ind<size*size; ind++){
	      result[ind] = ckpt_mem[RESULT+ind]; 
      }
      printf("restore from index %d\n", init_i);
    }

    for (i=init_i; i<size; i++){
      //      ckpt_1_label:       //label needeed for restoration
      for (j=i; j<size; j++){
        sum=result[i*size+j];
        for (k=0; k<i; k++) sum -= result[i*size+k]*result[k*size+j];
        result[i*size+j]=sum;
      }
      
      for (j=i+1;j<size; j++){
        sum=result[j*size+i];
        for (k=0; k<i; k++) sum -= result[j*size+k]*result[k*size+i];
        result[j*size+i]=sum/result[i*size+i];
      }

      #ifdef FPGA_TARGET
        if((i%10) == 0)
          checkpoint(ckpt_mem, i, result, size, 1, 1);
      #endif

      //if((ckpt_id == 0) && (i>300))
      //return;
      
    }

    //completed[0] = 1;
    ckpt_mem[COMPLETED] = 1;
    return;
  }
  
  void workload(float result[1024*1024], int size, float ckpt_mem[1024*1024+CKPT_SIZE])
  {

    #pragma HLS INTERFACE m_axi port=result offset=slave bundle=gmem
    #pragma HLS INTERFACE m_axi port=ckpt_mem offset=slave bundle=gmem
    #pragma HLS INTERFACE s_axilite port=result bundle=control
    #pragma HLS INTERFACE s_axilite port=size bundle=control
    #pragma HLS INTERFACE s_axilite port=ckpt_mem bundle=control
    #pragma HLS INTERFACE s_axilite port=return bundle=control
    
    lud(result, size, ckpt_mem, ckpt_mem[CKPT_ID]);
        
    return;
    
  }
}
