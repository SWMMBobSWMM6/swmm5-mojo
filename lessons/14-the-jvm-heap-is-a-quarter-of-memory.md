The JVM's default heap is a quarter of the machine's memory; a C program has all of it.

Java's first gate run crashed on Hydrology/sewer_rdii_problem.inp with "java.lang.OutOfMemoryError: Java heap
space" in rdii.c's allocRdiiMemory. The model has 613 RDII unit hydrograph groups whose long-term response lasts
9,900 hours (T = 900, K = 10), and rdii.c keeps each group's rainfall history at the one-minute wet step
(getRainInterval starts from WET_STEP), so the pastRain and pastMonth arrays come to 3.38 GB
(gate/rdii_memory.py); EPA itself peaks at 3.11 GB resident on it. The JVM here chose a 1.5 GB maximum heap (25%
of what it sees). Raising it to 75% with the default G1 collector still failed; with `-XX:+UseParallelGC
-XX:MaxRAMPercentage=75` it runs (4.92 GB peak resident) and matches EPA. TypeScript passed the same model with
no flags (3.23 GB peak), because Node keeps typed arrays outside V8's heap limit. Peaks:
gate/results/peak_memory.txt.

So the Java repository ships a launcher, `java/runswmm`, with those two flags, and the final Java gate ran
through it. Running the jar with a bare `java -jar` works for every other corpus model.
