
import constantine/math/arithmetic except Fp, Fr

import ./bn128

#-------------------------------------------------------------------------------

type 

  GrothHeader* = object
    curve*         : string
    p*             : BigInt[256]
    r*             : BigInt[256] 
    nvars*         : int
    npubs*         : int
    domainSize*    : int
    logDomainSize* : int

  SpecPoints* = object
    alpha1*      : G1
    beta1*       : G1
    beta2*       : G2
    gamma2*      : G2
    delta1*      : G1
    delta2*      : G2       
    alphaBeta*   : Fp12     # = <alpha1,beta2>

  VerifierPoints* = object
    pointsIC*    : seq[G1]

  ProverPoints* = object
    pointsA1*    : seq[G1]
    pointsB1*    : seq[G1]
    pointsB2*    : seq[G2]
    pointsC1*    : seq[G1]
    pointsH1*    : seq[G1]

  MatrixSel* = enum
    MatrixA
    MatrixB
    MatrixC

  Coeff* = object
    matrix* : MatrixSel
    row*    : int
    col*    : int
    coeff*  : Fr

  ZKey* = object
    # sectionMask* : uint32
    header*      : GrothHeader
    specPoints*  : SpecPoints
    vPoints*     : VerifierPoints
    pPoints*     : ProverPoints
    coeffs*      : seq[Coeff]

  VKey* = object 
    curve*   : string
    spec*    : SpecPoints
    vpoints* : VerifierPoints

#-------------------------------------------------------------------------------

func extractVKey*(zkey: Zkey): VKey = 
  let curve = zkey.header.curve
  let spec  = zkey.specPoints
  let vpts  = zkey.vPoints
  return VKey(curve:curve, spec:spec, vpoints:vpts)

#-------------------------------------------------------------------------------
