When the shared disk runs low, a gate's output folder can live in memory: only the model being checked needs room.

`gate.py --prune` deletes a passing model's outputs as soon as it is judged and keeps a failing model's, so a run
with many failures keeps all of them: one run of a port still being debugged kept 39 failing models' `.out` and
`.rpt` files, 754 MB, on a machine with about 1.9 GB free, and free space fell to about 430 MB, under the 1 GB
line the brief sets for stopping. The largest reference output in the corpus is 230 MB
(gate/ref_outputs/a4bb56859280), so a gate needs at least that much free at the moment it reaches that model.

The Kotlin gate (kt_1) ran with `gate/results/kt_1` as a symbolic link to a folder in `/dev/shm` (a tmpfs of
7.9 GB, in RAM), and `TMPDIR=/dev/shm` so the wrapper's backups of SAVE files went there too. The disk then held
nothing of the run but its JSON; RAM held one model's outputs at a time, since every model passed and was pruned.
After the run the link was replaced by an empty folder, as other runs leave it. The engine's own temporary files
(`swmmXXXXXX` in the model's folder) still go to the corpus disk, as EPA's do, and are removed when the run ends.

What to carry forward: the outputs of failing models are evidence (lesson 15), but on a small shared disk they are
also the largest thing a debugging run writes. Look at free space before starting a gate; when it is short, point
the run's output folder at memory, or delete superseded runs of your own, and say which you did. Never free space
from someone else's runs.
