# to be placed in the ex<num>/testing dir
# run as >> make LLVM=<path/to/llvm/install/>

CC=$(LLVM)/bin/clang++
OPT=$(LLVM)/bin/opt
CFLAGS = -pthread #-O1
INJECT?=save_restore

all : ex
.PHONY : all

lud.ll: ../lud.cpp
	#Dale:
	$(CC) -S $< -emit-llvm -o $@ -fno-discard-value-names -Xclang -disable-O0-optnone
	#Maxime:
	# $(CC) -S $< -emit-llvm -o $@

split_lud_out.ll: lud.ll
	#Dale:
	$(OPT) -load=/home/dalehuang/documents/junco-compiler_assisted_checkpointing-dale/build/lib/libSplitConditionalBB.so -load=/home/dalehuang/documents/junco-compiler_assisted_checkpointing-dale/build/lib/libLiveValues.so -load=/home/dalehuang/documents/junco-compiler_assisted_checkpointing-dale/build/lib/libSubroutineInjection.so -split-conditional-bb -S $< -live-values -source ../lud.cpp -subroutine-injection -o $@ -inject $(INJECT)
	#Maxime:
	# $(OPT) -load=/home/mfrance/hw-sw-migration/junco-compiler_assisted_checkpointing/build_llvm_7/lib/libSplitConditionalBB.so -load=/home/mfrance/hw-sw-migration/junco-compiler_assisted_checkpointing/build_llvm_7/lib/libLiveValues.so -load=/home/mfrance/hw-sw-migration/junco-compiler_assisted_checkpointing/build_llvm_7/lib/libSubroutineInjection.so -split-conditional-bb -S $< -live-values -source ../lud.cpp -subroutine-injection -o $@ -inject $(INJECT)

my_timer.o: ../my_timer.cpp
	$(CC) -c -o $@ $< $(CFLAGS)

local_support.o: ../local_support_sequential.cpp #../local_support.cpp
	$(CC) -c -o $@ $< $(CFLAGS)

lud.o: split_lud_out.ll
	$(CC) -c $< -o $@ $(CFLAGS)

ex: local_support.o lud.o my_timer.o
	$(CC) -o $@ $^ $(CFLAGS)

clean:
	rm -f *.o *~ ex *.ll *.json *.txt
