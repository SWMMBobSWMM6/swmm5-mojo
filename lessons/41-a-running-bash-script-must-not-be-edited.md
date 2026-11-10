Bash reads a script as it runs it: editing a job's script while the job waits inside it can make the job run fragments.

The gate chunk runners (`lua/gate/run_chunk.sh` and the others) are bash scripts that sit inside `flock` for up to an
hour and a half waiting for the corpus lock, then run the gate, then clean up (remove a symlink, copy the failing
models' outputs, delete the memory folder). While one Lua job was waiting, the script was edited to take one more
argument: a comment and an assignment were added near the top, about 150 bytes. The edit was noticed and the original
bytes were put back before the lock came free, so nothing went wrong, but it would have.

Bash does not read the whole script first. It reads and runs it command by command, and before running a command it
leaves the file offset just after that command; when the command returns, it reads on from that offset in whatever the
file now holds. A test (bash 5.2):

    #!/bin/bash
    # job.sh
    sleep 2
    echo "step 2: cleanup of $HOME/x would go here"
    echo "done"

started, and during the `sleep` two lines were added under the first comment. The job printed

    ./job.sh: line 4: er: command not found

and nothing else: it resumed in the middle of a line of the new file, ran the fragment `er...` as a command, and
skipped both echoes. In a script whose next lines are `rm -rf "$M"` and `cp -a`, a fragment can be a different command
from any the script contains.

What to take from it: never edit a script that a queued or running job is executing. Copy it, or give the change a new
file name, and edit the script only when no job is inside it (`ps` shows the jobs). Restoring the exact old bytes is
safe; the same content at the same offsets is the same script.
