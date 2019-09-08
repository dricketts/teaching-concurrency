# teaching-concurrency

This repository contains specifications and safety proofs of a simple concurrent algorithm that first appeared in the note "Teaching Concurrency" published in the March 2009 issue of ACM SIGACT News: http://lamport.azurewebsites.net/pubs/teaching-concurrency.pdf. In this algorithm, there are N processes and two arrays of length N, x and y. Each process i executes the following sequence of statements:

```
x[i] := 1;
y[i] := x[(i-1) mod N];
```

The reads and writes of each `x[j]` are assumed to be atomic. This algorithm has the property that once all processes have finished, at least one `y[j] = 1`.

The specification and safety proofs are written in several different languages. My goal is to compare concurrency reasoning in various verification tools. So far, I've written specs and proofs in the following tools:

* PlusCal/TLA+ (https://github.com/tlaplus/tlaplus)
* Dafny (https://github.com/dafny-lang/dafny)
* CIVL/Boogie (https://github.com/boogie-org/boogie)
* mypyvy (https://github.com/wilcoxjay/mypyvy)

I'd be happy to get feedback on my existing solutions, suggestions on other tools to try, or contributions in other tools.
