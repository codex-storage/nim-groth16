# Compile Example

This folder uses modified `fr` files from [witnesscalc](https://github.com/0xPolygonID/witnesscalc). These files modify the Circom generated circutes to support compilation on ARM64. This involves adding a `fr_raw_arm64.s` and `fr_raw_generic` to implement the required `fr` operations. It also changes some types to signed/unsigned to match the ARM versions.

Requires `gmp` and `nlohmann-json` to be installed and usable from `pkg-config`. On macos you can install them using: `brew install gmp nlohmann-json`.

To build:

```sh
cd example/circom_build/
nim cpp product.nim
./product
```
