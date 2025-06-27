# dilemma-artifact

This aritfact currently has 14 benchmarks sets that our tool was evaluated on (there are approximately two more that are expected to
be added as a result of the revisions). The table below details the number of benchmarks in each suite, as well as the number of "_groupings_" 
within that benchmark. A "_grouping_" is a set of benchmarks within a benchmark suite that is expected to run in at most approximately 20 minutes 
(except in cases where a single benchmark takes more than 20 minutes).

| Benchmark Suite               | Number of Test Locations    | Number of ~20 min Groups |
| :------------------:            | :------------------------:  | :------------------------:|
|       clam_implication        |      20                     |       1          |
|       clam_atomic             |      151                    |       14         |
|       lia_implication         |      9                      |       3          |
|       lia_atomic              |      29                     |       5          |
|       bagperm                 |      11                     |       1          |
|       binom                   |      46                     |       16         |
|       merge                   |      17                     |       3          |
|       perm                    |      1                      |       1          |
|       priqueue                |      8                      |       1          |
|       redblack                |      32                     |       8          |
|       searchtree              |      59                     |       13         |
|       selection               |      24                     |       2          |
|       sort                    |      11                     |       1          |
|       trie                    |      17                     |       1          |

## running instructions
```
    $ docker load -i <path to the tar>
    $ docker run -ti -v ${PWD}/results:/root/dilemma-artifact/results dilemma-artifact
    $ # bash run.sh <suite to run> 
        OR # bash run.sh group <group to run>
```