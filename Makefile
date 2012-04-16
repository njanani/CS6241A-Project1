# Makefile for hello pass

# Path to top level of LLVM hierarchy
LEVEL = ../../..

# Name of the library to build
LIBRARYNAME = abc

# Make the shared library become a loadable module so the tools can 
# dlopen/dlsym on the resulting library.
LOADABLE_MODULE = 1
LLVMLIBS = LLVMSupport.a

# Include the makefile implementation stuff
include $(LEVEL)/Makefile.common
