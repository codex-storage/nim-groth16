
import ./r1cs
import ./zkey
import ./witness
import ./bn128

#-------------------------------------------------------------------------------

proc testMain() = 
  # checkMontgomeryConstants()
  let r1cs_fname : string = "/Users/bkomuves/zk/examples/circom/toy/build/toymain.r1cs"
  let zkey_fname : string = "/Users/bkomuves/zk/examples/circom/toy/build/toymain.zkey"
  let wtns_fname : string = "/Users/bkomuves/zk/examples/circom/toy/build/toymain_witness.wtns"
  parseWitness( wtns_fname)
  parseR1CS(    r1cs_fname)
  parseZKey(    zkey_fname)

when isMainModule:
  testMain()