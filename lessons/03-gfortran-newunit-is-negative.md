gfortran's NEWUNIT= hands out negative unit numbers, so "unit < 0 means closed" silently discards a file.

The first Fortran run simulated a whole model and wrote empty .rpt and .out files. crt_io's flush and
fclose treated `unit < 0` as "no file open", and gfortran's `open(newunit=u, ...)` returns -10, -11, ...
Every buffered byte was dropped at close. The CFile type now carries an explicit `is_open` flag. Rule:
never encode state in the sign or range of a value the compiler chooses.
