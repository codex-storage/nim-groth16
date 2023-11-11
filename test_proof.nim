
import ./groth16
import ./witness
import ./zkey
import ./zkey_types

#-------------------------------------------------------------------------------

proc testProveAndVerify*( zkey_fname, wtns_fname: string): Proof = 

  echo("parsing witness & zkey files...")
  let witness = parseWitness( wtns_fname)
  let zkey    = parseZKey( zkey_fname)

  echo("generating proof...")
  let vkey  = extractVKey( zkey)
  let proof = generateProof( zkey, witness )

  echo("verifying the proof...")
  let ok = verifyProof( vkey, proof)
  echo("verification succeeded = ",ok)

  return proof

#-------------------------------------------------------------------------------
