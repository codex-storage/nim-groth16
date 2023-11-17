
#
# Groth16 prover
#
# WARNING! 
# the points H in `.zkey` are *NOT* what normal people would think they are
# See <https://geometry.xyz/notebook/the-hidden-little-secret-in-snarkjs>
#

#[
import sugar
import constantine/math/config/curves 
import constantine/math/io/io_fields
import constantine/math/io/io_bigints
import ./zkey
]#

# import constantine/math/arithmetic except Fp, Fr
import constantine/math/io/io_extfields except Fp12
import constantine/math/extension_fields/towers except Fp2, Fp12  

import groth16/bn128
import groth16/zkey_types

from groth16/prover import Proof

#-------------------------------------------------------------------------------
# the verifier
#

proc verifyProof* (vkey: VKey, prf: Proof): bool =

  assert( prf.curve == "bn128" )

  assert( isOnCurveG1(prf.pi_a) , "pi_a is not in G1" )
  assert( isOnCurveG2(prf.pi_b) , "pi_b is not in G2" )
  assert( isOnCurveG1(prf.pi_c) , "pi_c is not in G1" )

  var pubG1 : G1 = msmG1( prf.publicIO , vkey.vpoints.pointsIC )  

  let lhs   : Fp12 = pairing( negG1(prf.pi_a) , prf.pi_b )          # < -pi_a   , pi_b  >
  let rhs1  : Fp12 = vkey.spec.alphaBeta                            # < alpha  , beta  >
  let rhs2  : Fp12 = pairing( prf.pi_c , vkey.spec.delta2 )         # < pi_c   , delta >
  let rhs3  : Fp12 = pairing( pubG1    , vkey.spec.gamma2 )         # < sum... , gamma >

  var eq : Fp12
  eq =  lhs  
  eq *= rhs1
  eq *= rhs2
  eq *= rhs3

  return bool(isOne(eq))

#-------------------------------------------------------------------------------
