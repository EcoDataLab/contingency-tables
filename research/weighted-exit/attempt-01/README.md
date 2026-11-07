# Preserved initial compile failure

A reused nonnegativity lemma required a `Nonempty D` instance. The supplied
fallback already inhabits D; the successful proof derives that instance
locally, without adding a premise. An unreachable `ring` tactic was also
removed. No audit ran for the failed attempt. Source bytes are unchanged;
diagnostic paths and trailing whitespace are projected for public replay.
