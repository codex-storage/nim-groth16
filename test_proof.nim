

import std/[times, os]

import ./groth16
import ./witness
import ./r1cs
import ./zkey
import ./zkey_types
import ./fake_setup

#-------------------------------------------------------------------------------

proc testProveAndVerify*( zkey_fname, wtns_fname: string): Proof = 

  echo("parsing witness & zkey files...")
  let witness = parseWitness( wtns_fname)
  let zkey    = parseZKey( zkey_fname)

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

  return proof

#-------------------------------------------------------------------------------

proc testFakeSetupAndVerify*( r1cs_fname, wtns_fname: string, flavour=Snarkjs): Proof = 
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

  return proof
