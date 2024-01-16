
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

import constantine/math/arithmetic except Fp, Fr
#import constantine/math/io/io_extfields except Fp12
#import constantine/math/extension_fields/towers except Fp2, Fp12  

import groth16/bn128
import groth16/math/domain
import groth16/math/poly
import groth16/zkey_types
import groth16/files/witness

#-------------------------------------------------------------------------------

type
  Proof* = object
    publicIO* : seq[Fr]
    pi_a*     : G1
    pi_b*     : G2
    pi_c*     : G1
    curve*    : string

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
  for i in 0..<domSize:
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
  let eta   = createDomain(2*n).domainGen
  let invZ1 = invFr( smallPowFr(eta,n) - oneFr )

  let A1   = shiftEvalDomain( abc.valuesA, D, eta )
  let B1   = shiftEvalDomain( abc.valuesB, D, eta )
  let C1   = shiftEvalDomain( abc.valuesC, D, eta )

  var ys : seq[Fr] = newSeq[Fr]( n )
  for j in 0..<n: ys[j] = ( A1[j]*B1[j] - C1[j] ) * invZ1
  let Q1 = polyInverseNTT( ys, D )

  let cs = multiplyByPowers( Q1.coeffs, invFr(eta) )
  return Poly(coeffs: cs)

#---------------------------------------

# Snarkjs does something different, not actually computing the quotient poly
# they can get away with this, because during the trusted setup, they
# replace the points encoding the values `delta^-1 * tau^i * Z(tau)` by 
# (shifted) Lagrange bases.
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

type
  Mask* = object
    r*: Fr              # masking coefficients 
    s*: Fr              # for zero knowledge

proc generateProofWithMask*( zkey: ZKey, wtns: Witness, mask: Mask ): Proof =
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

  var qs : seq[Fr]
  case zkey.header.flavour

    # the points H are [delta^-1 * tau^i * Z(tau)]
    of JensGroth:
      let polyQ = computeQuotientPointwise( abc )
      qs = polyQ.coeffs

    # the points H are `[delta^-1 * L_{2i+1}(tau)]_1`
    # where L_i are Lagrange basis polynomials on the double-sized domain
    of Snarkjs:
      qs = computeSnarkjsScalarCoeffs( abc )

  var zs : seq[Fr] = newSeq[Fr]( nvars - npubs - 1 )
  for j in npubs+1..<nvars:
    zs[j-npubs-1] = witness[j]

  # masking coeffs
  let r = mask.r
  let s = mask.s

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

proc generateProof*( zkey: ZKey, wtns: Witness ): Proof =

  # masking coeffs
  let r : Fr = randFr()
  let s : Fr = randFr()
  let mask = Mask(r: r, s: s)

  return generateProofWithMask( zkey, wtns, mask )
