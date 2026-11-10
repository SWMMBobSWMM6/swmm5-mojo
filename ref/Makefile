# EPA SWMM 5.2.4 reference build: serial, gcc -O2, glibc libm, no FMA contraction, no _FORTIFY_SOURCE
SRC=epa524/solver
runswmm: $(wildcard $(SRC)/*.c) epa524/run/main.c
	gcc -O2 -U_FORTIFY_SOURCE -D_FORTIFY_SOURCE=0 -I$(SRC) -I$(SRC)/include $(SRC)/*.c epa524/run/main.c -o $@ -lm
