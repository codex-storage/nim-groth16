
import std/unittest
import std/sequtils

import groth16/prover
import groth16/verifier
import groth16/fake_setup
import groth16/zkey_types
import groth16/files/witness
import groth16/files/r1cs
import groth16/bn128/fields

#-------------------------------------------------------------------------------
# simple hand-crafted arithmetic circuit
#

const myWitnessCfg =
  WitnessConfig( nWires:  7
               , nPubOut: 1       # public output = input + a*b*c = 1022 + 7*11*13 = 2023
               , nPubIn:  1       # public input  = 1022
               , nPrivIn: 3       # private inputs: 7, 11, 13
               , nLabels: 0 
               )

# 2023 == 1022 + 7*3*11
const myEq1 : Constraint = ( @[] , @[] , @[ (0,minusOneFr) , (1,oneFr) , (6,oneFr) ] )

# 7*11 == 77
const myEq2 : Constraint = ( @[ (2,oneFr) ] , @[ (3,oneFr) ] , @[ (5,oneFr) ] )

# 77*13 == 1001
const myEq3 : Constraint = ( @[ (4,oneFr) ] , @[ (5,oneFr) ] , @[ (6,oneFr) ] )

const myConstraints : seq[Constraint] = @[ myEq1, myEq2, myEq3 ]

const myLabels : seq[int] = @[]

const myR1CS =
  R1CS( r:            primeR
      , cfg:          myWitnessCfg
      , nConstr:      myConstraints.len
      , constraints:  myConstraints
      , wireToLabel:  myLabels
      )

# the equation we want prove is `7*11*13 + 1022 == 2023`
let myWitnessValues : seq[Fr] = map( @[ 2023, 1022, 7, 11, 13, 7*11, 7*11*13 ] , intToFr )
# wire indices:         ^^^^^^^             0     1    2  3   4    5      6

let myWitness = 
  Witness( curve:  "bn128"
         , r:      primeR
         , nvars:  7
         , values: myWitnessValues
         )

#-------------------------------------------------------------------------------

proc testProof(zkey: ZKey, witness: Witness): bool = 
  let proof = generateProof( zkey, witness )
  let vkey  = extractVKey( zkey)
  let ok    = verifyProof( vkey, proof )
  return ok

suite "prover":

  test "prove & verify simple multiplication circuit, `JensGroth` flavour":
    let zkey = createFakeCircuitSetup( myR1cs, flavour=JensGroth ) 
    check testProof( zkey, myWitness )

  test "prove & verify simple multiplication circuit, `Snarkjs` flavour":
    let zkey = createFakeCircuitSetup( myR1cs, flavour=Snarkjs ) 
    check testProof( zkey, myWitness )

#-------------------------------------------------------------------------------
