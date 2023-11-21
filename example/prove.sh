#!/bin/bash

ORIG=`pwd`
NAME="product"

# --- create build directory ---
mkdir -p build

# --- compile the circom code ---
cd ${ORIG}
circom --r1cs --wasm --c -o build ${NAME}.circom

# --- download powers-of-tau ceremony, if necessary ---
cd ${ORIG}/build
PTAU_FILE="power_of_tau_10.ptau"
if ! test -f ./${PTAU_FILE}; then
  echo "downloading powers-of-tau..."
  curl https://hermez.s3-eu-west-1.amazonaws.com/powersOfTau28_hez_final_10.ptau --output $PTAU_FILE
else
  echo "powers-of-tau file already exists, skip downloading"
fi
PTAU_FILE="`pwd`/${PTAU_FILE}"

# --- perform circuit-specific setup ---
cd ${ORIG}/build
snarkjs groth16 setup ${NAME}.r1cs $PTAU_FILE ${NAME}_0000.zkey
echo "foobar entropy" | \
  snarkjs zkey contribute ${NAME}_0000.zkey ${NAME}_0001.zkey --name="1st Contributor Name" -v
echo "baz entropy" | \
  snarkjs zkey contribute ${NAME}_0001.zkey ${NAME}_0002.zkey --name="2nd Contributor Name" -v
rm ${NAME}_0000.zkey
rm ${NAME}_0001.zkey
mv ${NAME}_0002.zkey ${NAME}.zkey

# --- export vericiation key ---
cd ${ORIG}/build
snarkjs zkey export verificationkey ${NAME}.zkey ${NAME}_vkey.json

# --- create public input ---
cd $ORIG
echo '{ "inp": [7,11,13] , "plus": 1022 }' >build/${NAME}_input.json

# --- generate witness ---
cd $ORIG/build/${NAME}_js
node generate_witness.js ${NAME}.wasm ../${NAME}_input.json ../${NAME}.wtns
cd $ORIG/build

# --- create proof with snarkjs ---
# echo "creating the proof with snarkjs..."
# snarkjs groth16 prove ${NAME}.zkey ${NAME}.wtns snarkjs_proof.json snarkjs_public.json

# --- build & execute nim prover ---
cd $ORIG
echo "building and executing the Nim prover..."
nim c -r --processing:off example.nim

cd $ORIG/build
echo "verifying the proof with snarkjs..."
snarkjs groth16 verify ${NAME}_vkey.json nim_public.json nim_proof.json

cd $ORIG

