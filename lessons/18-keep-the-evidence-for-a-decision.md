Keep the measurement behind a decision with the work, not in a scratch folder; otherwise the decision reads as an opinion.

Go was chosen as the sixth port after a quick survey: four languages from the Code Rosetta Stone app (Go, Perl,
Ruby, Free Pascal) had their own math functions and their own printf compared with glibc. The survey ran in a
scratch folder and its results stayed there. When a second Claude instance audited the essay against the stored
evidence, it could not find the survey and marked the sentence about it unsupported. It was right to: nothing in
the repository showed what the survey measured.

Looking again also corrected the sentence. The essay said Go "came out ahead". The numbers say otherwise on one
point: Perl matched glibc on both tests, because it hands its math and its printf to the C library. Go matched on
printf and not on math (`pow` differs on 45,738 of 100,000 arguments). Go still had what the work needed: a printf that
matched, machine code, and math that the existing glibc translation could replace. That made it a choice, not a win.

The survey now lives in `gate/lang_survey/`, `gate/lang_survey.sh` reruns it, and the result is
`gate/results/lang_survey.txt`. The rerun reproduced the scratch numbers exactly.

What to carry forward: when a measurement decides what gets built, copy it into the repository the moment the
decision is made, with a script that repeats it. Then say what it showed, not what you remember it showed.
