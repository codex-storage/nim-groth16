
Groth16 prover written in Nim
-----------------------------

This is Groth16 prover implementation in Nim, using the 
[`constantine`](https://github.com/mratsim/constantine)
library as an arithmetic / curve backend.

The implementation is compatible with the `circom` + `snarkjs` ecosystem.

At the moment only the `BN254` (aka. `alt-bn128`) curve is supported.

### License

Licensed and distributed under either of the
[MIT license](http://opensource.org/licenses/MIT) or
[Apache License, v2.0](http://www.apache.org/licenses/LICENSE-2.0),
at your choice. 

### TODO

- [ ] make it a nimble package
- [ ] refactor `bn128.nim` into smaller files
- [ ] proper MSM implementation (I couldn't make constantine's one to work)
- [x] compare `.r1cs` to the "coeffs" section of `.zkey`
- [x] generate fake circuit-specific setup ourselves
- [ ] multithreaded support (MSM, and possibly also FFT)
- [ ] add Groth16 notes
- [ ] document the `snarkjs` circuit-specific setup `H` points convention
- [ ] make it work for different curves

