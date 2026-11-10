Before downloading a compiler, look for one the machine already has: Gradle carries a Kotlin compiler.

The Kotlin and Scala ports were to be built with compilers fetched from Maven Central. This sandbox refused
Maven Central outright (`repo1.maven.org` and `repo.maven.apache.org` answer 403 at the proxy). npm was allowed
and carries JetBrains' own `kotlin-compiler` package (2.4.21, the full kotlinc distribution), but running a
compiler downloaded that way was refused by the session's safety check as code from outside, the same check
that kept the libm work from running anything built from glibc's source (lesson 12). The download was deleted.

Gradle 8.14.3 was already installed, and Gradle compiles its Kotlin build scripts with a Kotlin compiler it
ships: `/opt/gradle/lib/kotlin-compiler-embeddable-2.0.21.jar`, with `kotlin-stdlib-2.0.21.jar` and the few
jars the compiler needs beside it. `java -cp <those jars> org.jetbrains.kotlin.cli.jvm.K2JVMCompiler` is a
complete Kotlin 2.0.21 JVM compiler; it built the whole port in about 40 seconds (`kotlin/build.sh`).

Nothing equivalent exists for Scala: no Scala compiler or library is installed anywhere on the machine, and
neither npm nor PyPI carries an official one, so the Scala port could not be built or gated here. It needs
Maven Central (or a Scala installation) allowed for the session.

What to carry forward: when a registry refuses, list what is installed (`find / -name '*compiler*.jar'`,
the lib folders of Gradle, Maven, IDEs) before concluding a language is unavailable, and record which copy
was used, because a compiler that ships inside another tool is easy to miss and its version is not the
latest (2.0.21 here, while 2.4.21 was current).
