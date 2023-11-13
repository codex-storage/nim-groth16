import pkg/groth16

import ../tests/test_proof
import ../src/export_json

let zkey_fname : string = "./build/product.zkey"
let wtns_fname : string = "./build/product.wtns"
let proof = testProveAndVerify( zkey_fname, wtns_fname)

exportPublicIO( "./build/nim_public.json" , proof )
exportProof(    "./build/nim_proof.json"  , proof )
