The app re-derives every verdict from the engines' output files, so those files are evidence, not scratch.

`tools/app/build_data.py` does not trust a gate run's PASS: it re-hashes each engine's `r.out` and `r.rpt`
against EPA's and turns any mismatch into RECHECK-FAIL. Short of disk during the TypeScript and Java runs,
I deleted the output folders of runs whose JSON had been written, including the two final runs. The JSON
still said 480 of 480, but nothing could check it any more, and both final gates had to be run again to put
the files back. Delete outputs only of runs nothing reads (superseded runs, controls that are counted from
their JSON), and when disk is short, say so and choose, rather than freeing it from the evidence.
