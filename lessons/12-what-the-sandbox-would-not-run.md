Two actions were refused by the session's safety checks; the work went around them without trying to defeat them.

1. Creating public GitHub repositories from the browser was refused ("create public surface"). Bob created
   the repositories himself; the session then pushed to them.
2. Running a program compiled from the downloaded glibc source was refused ("code from external"). The
   libm work therefore never executes glibc's code: tools/libm/build_glibm.sh only compiles it (to get
   GCC's GIMPLE dumps and the object files), tools/libm/extract_tables.py reads the constant tables out of
   the object files with objdump/objcopy, and the reference values come from the system's own libm (the
   one EPA links against), called by a test program written here (tools/libm/test/mkvectors.c).

Plan for both from the start: repository creation is Bob's step, and anything built from third-party
source is input data, not something to run.
