A C# lambda parameter named like a local silently assigns to itself.

The first C# gate failed three rain-file models (every value "missing") because the sscanf targets were
emitted as `R.RefL(v => v = v)` inside a function that has a local `long v`. Newer C# allows a lambda
parameter to shadow a local, so the assignment went to the lambda's own parameter and the local stayed
at its initial 99999. Generated lambdas now use parameter names that cannot clash (`__v`). Rule: any name
the translator invents must live in a namespace C identifiers cannot reach (leading double underscore).
