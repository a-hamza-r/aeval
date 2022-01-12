clang-10 -c -emit-llvm -m64 -S -O3 -fstrict-aliasing -fvectorize -Rpass=loop-vectorize -Rpass-missed=loop-vectorize -fslp-vectorize -ffast-math -fopenmp=libomp $1.c -o $1.ll

# -mllvm -force-vector-width=#
