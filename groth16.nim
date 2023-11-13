import pkg/results

import pkg/groth16
import pkg/witness
import pkg/zkey
import pkg/zkey_types
import pkg/export_json

export groth16, witness, zkey, zkey_types, export_json

#-------------------------------------------------------------------------------

proc proveAndVerify*( zkey_fname, wtns_fname: string): Result[Proof, cstring] =
  debugEcho("parsing witness & zkey files...")
  let witness = parseWitness( wtns_fname)
  let zkey    = parseZKey( zkey_fname)

  debugEcho("generating proof...")
  let vkey  = extractVKey( zkey)
  let proof = generateProof( zkey, witness )

  debugEcho("verifying the proof...")
  if verifyProof( vkey, proof):
    debugEcho("verification succeeded")
    ok proof
  else:
    err "verification failed"

#-------------------------------------------------------------------------------
