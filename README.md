
Groth16 prover in Nim
---------------------

This is Groth16 prover implementation in Nim, using the 
[`constantine`](https://github.com/mratsim/constantine)
library as an arithmetic / curve backend.

The implementation should be compatible with the `circom` ecosystem.

At the moment only the `BN254` (aka. `alt-bn128`) curve is supported.
