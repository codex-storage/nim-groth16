
#
# Groth16 prover
#
# WARNING! the points H are *NOT* what normal people would think they are
# See <https://geometry.xyz/notebook/the-hidden-little-secret-in-snarkjs>
#

#[]
import sugar
import constantine/math/config/curves 
import constantine/math/io/io_fields
import constantine/math/io/io_bigints
import ./zkey
]#

import constantine/math/arithmetic except Fp, Fr
import constantine/math/io/io_extfields except Fp12
import constantine/math/extension_fields/towers except Fp2, Fp12  

import ./bn128
import ./domain
import ./poly
import ./zkey_types
import ./witness

#-------------------------------------------------------------------------------

type
  Proof* = object
    publicIO* : seq[Fr]
    pi_a*     : G1
    pi_b*     : G2
    pi_c*     : G1
    curve     : string

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
# A, B, C column vectors
# 

type
  ABC = object
    valuesA : seq[Fr]
    valuesB : seq[Fr]
    valuesC : seq[Fr]

func buildABC( zkey: ZKey, witness: seq[Fr] ): ABC = 
  let hdr: GrothHeader = zkey.header
  let domSize = hdr.domainSize

  var valuesA : seq[Fr] = newSeq[Fr](domSize)
  var valuesB : seq[Fr] = newSeq[Fr](domSize)
  for entry in zkey.coeffs:
    case entry.matrix 
      of MatrixA: valuesA[entry.row] += entry.coeff * witness[entry.col]
      of MatrixB: valuesB[entry.row] += entry.coeff * witness[entry.col]
      else: raise newException(AssertionDefect, "fatal error")

  var valuesC : seq[Fr] = newSeq[Fr](domSize)
  for i in 0..<hdr.nvars:
    valuesC[i] = valuesA[i] * valuesB[i]

  return ABC( valuesA:valuesA, valuesB:valuesB, valuesC:valuesC )

#-------------------------------------------------------------------------------
# quotient poly
#

# interpolates A,B,C, and computes the quotient polynomial Q = (A*B - C) / Z
func computeQuotientNaive( abc: ABC ): Poly=
  let n = abc.valuesA.len
  assert( abc.valuesB.len == n )
  assert( abc.valuesC.len == n )
  let D = createDomain(n)
  let polyA : Poly = polyInverseNTT( abc.valuesA , D )
  let polyB : Poly = polyInverseNTT( abc.valuesB , D )
  let polyC : Poly = polyInverseNTT( abc.valuesC , D )
  let polyBig = polyMulFFT( polyA , polyB ) - polyC
  var polyQ   = polyDivideByVanishing(polyBig, D.domainSize)
  polyQ.coeffs.add( zeroFr )    # make it a power of two
  return polyQ

#---------------------------------------

# returns [ eta^i * xs[i] | i<-[0..n-1] ]
func multiplyByPowers( xs: seq[Fr], eta: Fr ): seq[Fr] = 
  let n = xs.len
  assert(n >= 1)
  var ys : seq[Fr] = newSeq[Fr](n)
  ys[0] = xs[0]
  if n >= 1: ys[1] = eta * xs[1]
  var spow : Fr = eta
  for i in 2..<n: 
    spow *= eta
    ys[i] = spow * xs[i]
  return ys

# interpolates a polynomial, shift the variable by `eta`, and compute the shifted values
func shiftEvalDomain( values: seq[Fr], D: Domain, eta: Fr ): seq[Fr] =
  let poly : Poly = polyInverseNTT( values , D )
  let cs : seq[Fr] = poly.coeffs
  var ds : seq[Fr] = multiplyByPowers( cs, eta )
  return polyForwardNTT( Poly(coeffs:ds), D )

# computes the quotient polynomial Q = (A*B - C) / Z
# by computing the values on a shifted domain, and interpolating the result
# remark: Q has degree `n-2`, so it's enough to use a domain of size n
func computeQuotientPointwise( abc: ABC ): Poly =
  let n    = abc.valuesA.len
  let D    = createDomain(n)
  
  # (eta*omega^j)^n - 1 = eta^n - 1 
  # 1 / [ (eta*omega^j)^n - 1] = 1/(eta^n - 1)
  let eta  = createDomain(2*n).domainGen
  let Inv1 = invFr( smallPowFr(eta,n) - oneFr )

  let A1   = shiftEvalDomain( abc.valuesA, D, eta )
  let B1   = shiftEvalDomain( abc.valuesB, D, eta )
  let C1   = shiftEvalDomain( abc.valuesC, D, eta )

  var ys : seq[Fr] = newSeq[Fr]( n )
  for j in 0..<n: ys[j] = ( A1[j]*B1[j] - C1[j] ) * Inv1
  let Q1 = polyInverseNTT( ys, D )

  let cs = multiplyByPowers( Q1.coeffs, invFr(eta) )
  return Poly(coeffs: cs)

#---------------------------------------

# Snarkjs does something different, not actually computing the quotient poly
# they can get away with this, because during the trusted setup, they
# transform the H points into (shifted??) Lagrange bases (?)
# see <https://geometry.xyz/notebook/the-hidden-little-secret-in-snarkjs>
#
func computeSnarkjsScalarCoeffs( abc: ABC ): seq[Fr] =
  let n    = abc.valuesA.len
  let D    = createDomain(n)
  let eta  = createDomain(2*n).domainGen
  let A1   = shiftEvalDomain( abc.valuesA, D, eta )
  let B1   = shiftEvalDomain( abc.valuesB, D, eta )
  let C1   = shiftEvalDomain( abc.valuesC, D, eta )
  var ys : seq[Fr] = newSeq[Fr]( n )
  for j in 0..<n: ys[j] = ( A1[j]*B1[j] - C1[j] ) 
  return ys

#-------------------------------------------------------------------------------
# the prover
#

proc generateProof* ( zkey: ZKey, wtns: Witness ): Proof =
  assert( zkey.header.curve == wtns.curve )

  let witness = wtns.values

  let hdr  : GrothHeader  = zkey.header
  let spec : SpecPoints   = zkey.specPoints
  let pts  : ProverPoints = zkey.pPoints     

  let nvars = hdr.nvars
  let npubs = hdr.npubs

  assert( nvars == witness.len , "wrong witness length" )

  var pubIO : seq[Fr] = newSeq[Fr]( npubs + 1)
  for i in 0..npubs: pubIO[i] = witness[i]

  var abc : ABC = buildABC( zkey, witness )

  # let polyQ1 =  computeQuotientNaive(     abc )
  # let polyQ2 =  computeQuotientPointwise( abc )

  let qs = computeSnarkjsScalarCoeffs( abc )

  var zs : seq[Fr] = newSeq[Fr]( nvars - npubs - 1 )
  for j in npubs+1..<nvars:
    zs[j-npubs-1] = witness[j]

  # masking coeffs
  let r : Fr = randFr()
  let s : Fr = randFr()

  # let r : Fr = intToFr(3)
  # let s : Fr = intToFr(4)

  var pi_a : G1 
  pi_a =  spec.alpha1
  pi_a += r ** spec.delta1
  pi_a += msmG1( witness , pts.pointsA1 )

  var rho : G1 
  rho =  spec.beta1
  rho += s ** spec.delta1
  rho += msmG1( witness , pts.pointsB1 )

  var pi_b : G2
  pi_b =  spec.beta2
  pi_b += s ** spec.delta2
  pi_b += msmG2( witness , pts.pointsB2 )

  var pi_c : G1
  pi_c =  s ** pi_a
  pi_c += r ** rho
  pi_c += negFr(r*s) ** spec.delta1
  pi_c += msmG1( qs , pts.pointsH1 )
  pi_c += msmG1( zs , pts.pointsC1 )

  return Proof( curve:"bn128", publicIO:pubIO, pi_a:pi_a, pi_b:pi_b, pi_c:pi_c )

#-------------------------------------------------------------------------------
