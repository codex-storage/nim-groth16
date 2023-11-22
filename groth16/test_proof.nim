

import std/[times, os]

import groth16/prover
import groth16/verifier
import groth16/files/witness
import groth16/files/r1cs
import groth16/files/zkey
import groth16/zkey_types
import groth16/fake_setup

#-------------------------------------------------------------------------------

proc testProveAndVerify*( zkey_fname, wtns_fname: string): (VKey,Proof) = 

  echo("parsing witness & zkey files...")
  let witness = parseWitness( wtns_fname)
  let zkey    = parseZKey( zkey_fname)

  echo("generating proof...")
  let start = cpuTime()
  let proof = generateProof( zkey, witness )
  let elapsed = cpuTime() - start
  echo("proving took ",elapsed)

  echo("verifying the proof...")
  let vkey = extractVKey( zkey)
  let ok   = verifyProof( vkey, proof )
  echo("verification succeeded = ",ok)

  return (vkey,proof)

#-------------------------------------------------------------------------------

proc testFakeSetupAndVerify*( r1cs_fname, wtns_fname: string, flavour=Snarkjs): (VKey,Proof) = 
  echo("trusted setup flavour = ",flavour)

  echo("parsing witness & r1cs files...")
  let witness = parseWitness( wtns_fname)
  let r1cs    = parseR1CS( r1cs_fname)

  echo("performing fake trusted setup...")
  let zkey = createFakeCircuitSetup( r1cs, flavour=flavour )

  # printCoeffs(zkey.coeffs)

  echo("generating proof...")
  let vkey  = extractVKey( zkey)

  let start = cpuTime()
  let proof = generateProof( zkey, witness )
  let elapsed = cpuTime() - start
  echo("proving took ",elapsed)

  echo("verifying the proof...")
  let ok = verifyProof( vkey, proof )
  echo("verification succeeded = ",ok)

  return (vkey,proof)
