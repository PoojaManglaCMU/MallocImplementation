add-auto-load-safe-path /afs/andrew.cmu.edu/usr1/pmangla/courses/start_afresh/malloclab-handout/.gdbinit
b mm_init
b mm_malloc
b mm_free
b mm_check
run -f traces/bash.rep
