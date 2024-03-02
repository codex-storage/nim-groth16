
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

import std/os
import std/times
import std/cpuinfo
import system
import taskpools

import constantine/math/arithmetic except Fp, Fr
#import constantine/math/io/io_extfields except Fp12
#import constantine/math/extension_fields/towers except Fp2, Fp12  

import groth16/bn128
import groth16/math/domain
import groth16/math/poly
import groth16/zkey_types
import groth16/files/witness
import groth16/misc

#-------------------------------------------------------------------------------

type
  Proof* = object
    publicIO* : seq[Fr]
    pi_a*     : G1
    pi_b*     : G2
    pi_c*     : G1
    curve*    : string

#-------------------------------------------------------------------------------
# Az, Bz, Cz column vectors
# 

type
  ABC = object
    valuesAz : seq[Fr]
    valuesBz : seq[Fr]
    valuesCz : seq[Fr]

# computes the vectors A*z, B*z, C*z where z is the witness
func buildABC( zkey: ZKey, witness: seq[Fr] ): ABC = 
  let hdr: GrothHeader = zkey.header
  let domSize = hdr.domainSize

  var valuesAz : seq[Fr] = newSeq[Fr](domSize)
  var valuesBz : seq[Fr] = newSeq[Fr](domSize)

  for entry in zkey.coeffs:
    case entry.matrix 
      of MatrixA: valuesAz[entry.row] += entry.coeff * witness[entry.col]
      of MatrixB: valuesBz[entry.row] += entry.coeff * witness[entry.col]
      else: raise newException(AssertionDefect, "fatal error")

  var valuesCz : seq[Fr] = newSeq[Fr](domSize)
  for i in 0..<domSize:
    valuesCz[i] = valuesAz[i] * valuesBz[i]

  return ABC( valuesAz:valuesAz, valuesBz:valuesBz, valuesCz:valuesCz )

#-------------------------------------------------------------------------------
# quotient poly
#

# interpolates A,B,C, and computes the quotient polynomial Q = (A*B - C) / Z
func computeQuotientNaive( abc: ABC ): Poly=
  let n = abc.valuesAz.len
  assert( abc.valuesBz.len == n )
  assert( abc.valuesCz.len == n )
  let D = createDomain(n)
  let polyA : Poly = polyInverseNTT( abc.valuesAz , D )
  let polyB : Poly = polyInverseNTT( abc.valuesBz , D )
  let polyC : Poly = polyInverseNTT( abc.valuesCz , D )
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
  echo "task: abc.values: ", values[0].unsafeAddr.pointer.repr
  let poly : Poly = polyInverseNTT( values , D )
  let cs : seq[Fr] = poly.coeffs
  var ds : seq[Fr] = multiplyByPowers( cs, eta )
  return polyForwardNTT( Poly(coeffs:ds), D )

# computes the quotient polynomial Q = (A*B - C) / Z
# by computing the values on a shifted domain, and interpolating the result
# remark: Q has degree `n-2`, so it's enough to use a domain of size n
proc computeQuotientPointwise( nthreads: int, abc: ABC ): Poly =
  let n    = abc.valuesAz.len
  assert( abc.valuesBz.len == n )
  assert( abc.valuesCz.len == n )

  let D    = createDomain(n)
  
  # (eta*omega^j)^n - 1 = eta^n - 1 
  # 1 / [ (eta*omega^j)^n - 1] = 1/(eta^n - 1)
  let eta   = createDomain(2*n).domainGen
  let invZ1 = invFr( smallPowFr(eta,n) - oneFr )

  var pool = Taskpool.new(num_threads = nthreads)
  echo "main: abc.valuesAz: ", abc.valuesAz[0].unsafeAddr.pointer.repr
  echo "main: abc.valuesBz: ", abc.valuesBz[0].unsafeAddr.pointer.repr
  echo "main: abc.valuesCz: ", abc.valuesCz[0].unsafeAddr.pointer.repr
  var A1fv : FlowVar[seq[Fr]] = pool.spawn shiftEvalDomain( abc.valuesAz, D, eta )
  var B1fv : FlowVar[seq[Fr]] = pool.spawn shiftEvalDomain( abc.valuesBz, D, eta )
  var C1fv : FlowVar[seq[Fr]] = pool.spawn shiftEvalDomain( abc.valuesCz, D, eta )
  pool.syncAll() 
  let A1 = sync A1fv
  let B1 = sync B1fv
  let C1 = sync C1fv

  var ys : seq[Fr] = newSeq[Fr]( n )
  for j in 0..<n: ys[j] = ( A1[j]*B1[j] - C1[j] ) * invZ1
  let Q1 = polyInverseNTT( ys, D )
  let cs = multiplyByPowers( Q1.coeffs, invFr(eta) )

  pool.shutdown()
  return Poly(coeffs: cs)

#---------------------------------------

# Snarkjs does something different, not actually computing the quotient poly
# they can get away with this, because during the trusted setup, they
# replace the points encoding the values `delta^-1 * tau^i * Z(tau)` by 
# (shifted) Lagrange bases.
# see <https://geometry.xyz/notebook/the-hidden-little-secret-in-snarkjs>
#
proc computeSnarkjsScalarCoeffs( nthreads: int, abc: ABC ): seq[Fr] =
  let n    = abc.valuesAz.len
  assert( abc.valuesBz.len == n )
  assert( abc.valuesCz.len == n )
  let D    = createDomain(n)
  let eta  = createDomain(2*n).domainGen

  var pool = Taskpool.new(num_threads = nthreads)
  GCref(abc.valuesAz)
  GCref(abc.valuesBz)
  GCref(abc.valuesCz)
  var A1fv : FlowVar[seq[Fr]] = pool.spawn shiftEvalDomain( abc.valuesAz, D, eta )
  var B1fv : FlowVar[seq[Fr]] = pool.spawn shiftEvalDomain( abc.valuesBz, D, eta )
  var C1fv : FlowVar[seq[Fr]] = pool.spawn shiftEvalDomain( abc.valuesCz, D, eta )
  pool.syncAll() 
  GCunref(abc.valuesAz)
  GCunref(abc.valuesBz)
  GCunref(abc.valuesCz)
  let A1 = sync A1fv
  let B1 = sync B1fv
  let C1 = sync C1fv

  var ys : seq[Fr] = newSeq[Fr]( n )
  for j in 0..<n: ys[j] = ( A1[j] * B1[j] - C1[j] ) 

  pool.shutdown()
  return ys

#-------------------------------------------------------------------------------
# the prover
#

type
  Mask* = object
    r*: Fr              # masking coefficients 
    s*: Fr              # for zero knowledge

proc generateProofWithMask*( nthreads: int, printTimings: bool, zkey: ZKey, wtns: Witness, mask: Mask ): Proof =

  # if (zkey.header.curve != wtns.curve):
  #   echo( "zkey.header.curve = " & ($zkey.header.curve) )
  #   echo( "wtns.curve        = " & ($wtns.curve       ) )

  assert( zkey.header.curve == wtns.curve )
  var start : float = 0

  let witness = wtns.values

  let hdr  : GrothHeader  = zkey.header
  let spec : SpecPoints   = zkey.specPoints
  let pts  : ProverPoints = zkey.pPoints     

  let nvars = hdr.nvars
  let npubs = hdr.npubs

  assert( nvars == witness.len , "wrong witness length" )

  # remark: with the special variable "1" we actuall have (npub+1) public IO variables
  var pubIO : seq[Fr] = newSeq[Fr]( npubs + 1)
  for i in 0..npubs: pubIO[i] = witness[i]             

  start = cpuTime()
  var abc : ABC 
  withMeasureTime(printTimings,"building 'ABC'"):
    abc = buildABC( zkey, witness )

  start = cpuTime()
  var qs : seq[Fr]
  withMeasureTime(printTimings,"computing the quotient (FFTs)"):
    case zkey.header.flavour

      # the points H are [delta^-1 * tau^i * Z(tau)]
      of JensGroth:
        let polyQ = computeQuotientPointwise( nthreads, abc )
        qs = polyQ.coeffs
  
      # the points H are `[delta^-1 * L_{2i+1}(tau)]_1`
      # where L_i are Lagrange basis polynomials on the double-sized domain
      of Snarkjs:
        qs = computeSnarkjsScalarCoeffs( nthreads, abc )

  var zs : seq[Fr] = newSeq[Fr]( nvars - npubs - 1 )
  for j in npubs+1..<nvars:
    zs[j-npubs-1] = witness[j]

  # masking coeffs
  let r = mask.r
  let s = mask.s

  assert( witness.len == pts.pointsA1.len )
  assert( witness.len == pts.pointsB1.len )
  assert( witness.len == pts.pointsB2.len )
  assert( hdr.domainSize    == qs.len           )
  assert( hdr.domainSize    == pts.pointsH1.len )
  assert( nvars - npubs - 1 == zs.len           )
  assert( nvars - npubs - 1 == pts.pointsC1.len )

  var pi_a : G1 
  withMeasureTime(printTimings,"computing pi_A (G1 MSM)"):
    pi_a =  spec.alpha1
    pi_a += r ** spec.delta1
    pi_a += msmMultiThreadedG1( nthreads , witness , pts.pointsA1 )

  var rho : G1 
  withMeasureTime(printTimings,"computing rho (G1 MSM)"):
    rho =  spec.beta1
    rho += s ** spec.delta1
    rho += msmMultiThreadedG1( nthreads , witness , pts.pointsB1 )

  var pi_b : G2
  withMeasureTime(printTimings,"computing pi_B (G2 MSM)"):
    pi_b =  spec.beta2
    pi_b += s ** spec.delta2
    pi_b += msmMultiThreadedG2( nthreads , witness , pts.pointsB2 )

  var pi_c : G1
  withMeasureTime(printTimings,"computing pi_C (2x G1 MSM)"):
    pi_c =  s ** pi_a
    pi_c += r ** rho
    pi_c += negFr(r*s) ** spec.delta1
    pi_c += msmMultiThreadedG1( nthreads, qs , pts.pointsH1 )
    pi_c += msmMultiThreadedG1( nthreads, zs , pts.pointsC1 )

  return Proof( curve:"bn128", publicIO:pubIO, pi_a:pi_a, pi_b:pi_b, pi_c:pi_c )

#-------------------------------------------------------------------------------

proc generateProofWithTrivialMask*( nthreads: int, printTimings: bool, zkey: ZKey, wtns: Witness ): Proof =
  let mask = Mask(r: intToFr(0), s: intToFr(0))
  return generateProofWithMask( nthreads, printTimings, zkey, wtns, mask )

proc generateProof*( nthreads: int, printTimings: bool, zkey: ZKey, wtns: Witness ): Proof =

  # masking coeffs
  let r : Fr = randFr()
  let s : Fr = randFr()
  let mask = Mask(r: r, s: s)

  return generateProofWithMask( nthreads, printTimings, zkey, wtns, mask )
