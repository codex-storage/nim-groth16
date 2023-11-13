
import pkg/results
import ../groth16

proc main(): Result[void, cstring] =
  let zkey_fname : string = "./build/product.zkey"
  let wtns_fname : string = "./build/product.wtns"
  let proof = ? proveAndVerify( zkey_fname, wtns_fname)

  exportPublicIO( "./build/nim_public.json" , proof )
  exportProof(    "./build/nim_proof.json"  , proof )

  ok()

if main().isErr:
  raiseAssert "Error verifying proof"
