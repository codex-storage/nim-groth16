
Groth16 prover written in Nim
-----------------------------

This is Groth16 prover implementation in Nim, using the 
[`constantine`](https://github.com/mratsim/constantine)
library as an arithmetic / curve backend.

The implementation is compatible with the `circom` ecosystem.

At the moment only the `BN254` (aka. `alt-bn128`) curve is supported.


### TODO

- [ ] make it a nimble package
- [ ] proper MSM implementation (I couldn't make constantine's one to work)
- [ ] proper polynomial implemention (constantine's one is essentially missing)
- [ ] compare `.r1cs` to the "coeffs" section of `.zkey`
- [ ] make it work for different curves
- [ ] multithreaded support (MSM, and possibly also FFT)
- [ ] add Groth16 notes
- [ ] document the `snarkjs` circuit-specific setup `H` points convention

