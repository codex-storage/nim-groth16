
#
# create "fake" circuit-specific trusted setup for testing purposes
#
# by fake here I mean that no actual ceremoney is done, we just generate 
# some random toxic waste
# 

import sugar
import std/sequtils

import constantine/math/arithmetic except Fp, Fr

import bn128
import domain
import poly
import zkey_types
import r1cs
import misc

#-------------------------------------------------------------------------------

type 
  ToxicWaste = object
    alpha: Fr
    beta:  Fr
    gamma: Fr
    delta: Fr
    tau:   Fr

proc randomToxicWaste(): ToxicWaste = 
  let a = randFr()
  let b = randFr()
  let c = randFr()
  let d = randFr()
  let t = randFr()
  return ToxicWaste( alpha: a
                   , beta:  b
                   , gamma: c
                   , delta: d
                   , tau:   t )

#-------------------------------------------------------------------------------

func r1csToCoeffs*(r1cs: R1CS): seq[Coeff] = 
  var coeffs : seq[Coeff]
  let n = r1cs.constraints.len
  let p = r1cs.cfg.nPubIn + r1cs.cfg.nPubOut
  for i in 0..<n:
    let ct = r1cs.constraints[i]
    for term in ct.A:
      let c = Coeff(matrix:MatrixA, row:i, col:term.wireIdx, coeff:term.value)
      coeffs.add(c)
    for term in ct.B:
      let c = Coeff(matrix:MatrixB, row:i, col:term.wireIdx, coeff:term.value)
      coeffs.add(c)

  # Snarkjs adds some dummy coefficients to the matrix "A", for the public I/O
  # Let's emulate that here
  for i in n..n+p:
    let c = Coeff(matrix:MatrixA, row:i, col:i-n, coeff:oneFr)
    coeffs.add(c)

  return coeffs

#-------------------------------------------------------------------------------

type Column*[T] = seq[T]

type Matrix*[T] = seq[Column[T]]

type 
  Matrices* = object
    A* : Matrix[Fr]
    B* : Matrix[Fr]
    C* : Matrix[Fr]

func r1csToMatrices*(r1cs: R1CS): Matrices =
  let n = r1cs.constraints.len
  let m = r1cs.cfg.nWires
  let p = r1cs.cfg.nPubIn + r1cs.cfg.nPubOut

  let logDomSize = ceilingLog2(n+p+1)
  let domSize    = 1 shl logDomSize

  var matA, matB, matC: Matrix[Fr]
  for i in 0..<m:
    var colA = newSeq[Fr](domSize)
    var colB = newSeq[Fr](domSize)
    var colC = newSeq[Fr](domSize)
    matA.add( colA )
    matB.add( colB )
    matC.add( colC )

  for i in 0..<n:
    let ct = r1cs.constraints[i]
    for term in ct.A: matA[term.wireIdx][i] += term.value
    for term in ct.B: matB[term.wireIdx][i] += term.value
    for term in ct.C: matC[term.wireIdx][i] += term.value

  # Snarkjs adds some dummy coefficients to the matrix "A", for the public I/O
  # Let's emulate that here
  for i in n..n+p:
    matA[i-n][i] += oneFr

  return Matrices(A:matA, B:matB, C:matC)

#-------------------------------------------------------------------------------

func matricesToCoeffs*(matrices: Matrices): seq[Coeff] = 
  let n = matrices.A[0].len
  let m = matrices.A.len

  var coeffs : seq[Coeff]
  for i in 0..<n:
    for j in 0..<m:

      let a = matrices.A[j][i]
      if not bool(isZero(a)):
        let x = Coeff(matrix:MatrixA, row:i, col:j, coeff:a)
        coeffs.add(x)

      let b = matrices.B[j][i]
      if not bool(isZero(b)):
        let x = Coeff(matrix:MatrixB, row:i, col:j, coeff:b)
        coeffs.add(x)

  return coeffs

#-------------------------------------------------------------------------------

func fakeCircuitSetup*(r1cs: R1CS, toxic: ToxicWaste, flavour=Snarkjs): ZKey = 
 
  let neqs       = r1cs.constraints.len
  let npub       = r1cs.cfg.nPubIn + r1cs.cfg.nPubOut
  let logDomSize = ceilingLog2(neqs+npub+1)  
  let domSize    = 1 shl logDomSize

  let nvars = r1cs.cfg.nWires
  let npubs = r1cs.cfg.nPubOut + r1cs.cfg.nPubIn

  # echo("nvars  = ",nvars)
  # echo("npub   = ",npubs)
  # echo("neqs   = ",neqs)
  # echo("domain = ",domSize)

  let header = GrothHeader( curve:   "bn128"
                          , flavour: flavour
                          , p:       primeP
                          , r:       primeR
                          , nvars:   nvars
                          , npubs:   npubs
                          , domainSize:    domSize
                          , logDomainSize: logDomSize
                          )

  let spec = SpecPoints( alpha1    : toxic.alpha ** gen1
                       , beta1     : toxic.beta  ** gen1
                       , beta2     : toxic.beta  ** gen2
                       , gamma2    : toxic.gamma ** gen2
                       , delta1    : toxic.delta ** gen1
                       , delta2    : toxic.delta ** gen2
                       , alphaBeta : pairing( toxic.alpha ** gen1 , toxic.beta ** gen2 )  
                       )

  let matrices = r1csToMatrices(r1cs)
  let coeffs   = r1csToCoeffs( r1cs )
  # let coeffs   = matricesToCoeffs(matrices)

  let D : Domain = createDomain(domSize) 

  let polyAs : seq[Poly] = collect( newSeq , (for col in matrices.A: polyInverseNTT(col, D) ))
  let polyBs : seq[Poly] = collect( newSeq , (for col in matrices.B: polyInverseNTT(col, D) ))
  let polyCs : seq[Poly] = collect( newSeq , (for col in matrices.C: polyInverseNTT(col, D) ))

  let pointsA  : seq[G1] = collect( newSeq , (for p in polyAs: polyEvalAt(p, toxic.tau) ** gen1) )
  let pointsB1 : seq[G1] = collect( newSeq , (for p in polyBs: polyEvalAt(p, toxic.tau) ** gen1) )
  let pointsB2 : seq[G2] = collect( newSeq , (for p in polyBs: polyEvalAt(p, toxic.tau) ** gen2) )
  let pointsC  : seq[G1] = collect( newSeq , (for p in polyCs: polyEvalAt(p, toxic.tau) ** gen1) )

  let gammaInv : Fr = invFr(toxic.gamma)
  let deltaInv : Fr = invFr(toxic.delta)

  let pointsL  : seq[G1] = collect( newSeq , (for j in 0..npub: 
        gammaInv ** ( toxic.beta ** pointsA[j] + toxic.alpha ** pointsB1[j] + pointsC[j] ) ))

  let pointsK  : seq[G1] = collect( newSeq , (for j in npub+1..nvars-1: 
        deltaInv ** ( toxic.beta ** pointsA[j] + toxic.alpha ** pointsB1[j] + pointsC[j] ) ))
 
  let polyZ    = vanishingPoly(D)
  let ztauG1   = polyEvalAt(polyZ, toxic.tau) ** gen1

  var pointsH : seq[G1]
  case flavour 
    
    # in the original paper, these are the curve points
    #   [ delta^-1 * tau^i * Z(tau) ] 
    of JensGroth:
      pointsH = collect( newSeq , (for i in 0..<domSize: 
        (deltaInv * smallPowFr(toxic.tau,i)) ** ztauG1 ))

    # in the Snarkjs implementation, these are the curve points
    #   [ delta^-1 * L_{2i+1} (tau) ]
    # where L_k are the Lagrange polynomials on the refined domain
    of Snarkjs:
      let D2  : Domain = createDomain(2*domSize)
      let eta : Fr     = D2.domainGen

      pointsH = collect( newSeq , (for i in 0..<domSize: 
        (deltaInv * evalLagrangePolyAt(D2, 2*i+1, toxic.tau)) ** gen1 ))

  let vPoints = VerifierPoints( pointsIC: pointsL )

  let pPoints = ProverPoints( pointsA1: pointsA
                            , pointsB1: pointsB1 
                            , pointsB2: pointsB2 
                            , pointsC1: pointsK
                            , pointsH1: pointsH 
                            )

  return ZKey( header:     header
             , specPoints: spec
             , vPoints:    vPoints
             , pPoints:    pPoints
             , coeffs:     coeffs
             )
    
#-------------------------------------------------------------------------------

proc createFakeCircuitSetup*(r1cs: R1CS, flavour=Snarkjs): ZKey = 
  let toxic = randomToxicWaste()
  return fakeCircuitSetup(r1cs, toxic, flavour=flavour)

#-------------------------------------------------------------------------------
