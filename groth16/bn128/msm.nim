
#
# Multi-Scalar Multiplication (MSM)
# 

import system

# import constantine/curves_primitives except Fp, Fp2, Fr
 
import constantine/platforms/abstractions   except Subgroup
import constantine/math/isogenies/frobenius except Subgroup

import constantine/math/arithmetic     except Fp, Fp2, Fr
import constantine/math/io/io_fields   except Fp, Fp2, Fr
import constantine/math/io/io_bigints
import constantine/math/config/curves  except G1, G2, Subgroup
import constantine/math/config/type_ff except Fp, Fr, Subgroup

import constantine/math/extension_fields/towers                 as ext except Fp, Fp2, Fp12, Fr
import constantine/math/elliptic/ec_shortweierstrass_affine     as aff except Subgroup
import constantine/math/elliptic/ec_shortweierstrass_projective as prj except Subgroup
import constantine/math/elliptic/ec_scalar_mul_vartime          as scl except Subgroup
import constantine/math/elliptic/ec_multi_scalar_mul            as msm except Subgroup

import groth16/bn128/fields
import groth16/bn128/curves

#-------------------------------------------------------------------------------

func msmConstantineG1*( coeffs: openArray[Fr] , points: openArray[G1] ): G1 =

  let N = coeffs.len
  assert( N == points.len, "incompatible sequence lengths" )

  var bigcfs : seq[BigInt[254]]
  for x in coeffs:
    bigcfs.add( x.toBig() )

  var r : ProjG1

  # [Fp,aff.G1]
  msm.multiScalarMul_vartime( r,
    toOpenArray(bigcfs, 0, N-1),
    toOpenArray(points, 0, N-1) )

  var rAff: G1
  prj.affine(rAff, r)

  return rAff

#---------------------------------------

func msmConstantineG2*( coeffs: openArray[Fr] , points: openArray[G2] ): G2 =

  let N = coeffs.len
  assert( N == points.len, "incompatible sequence lengths" )

  var bigcfs : seq[BigInt[254]]
  for x in coeffs:
    bigcfs.add( x.toBig() )

  var r : ProjG2

  # [Fp,aff.G1]
  msm.multiScalarMul_vartime( r,
    toOpenArray(bigcfs, 0, N-1),
    toOpenArray(points, 0, N-1) )

  var rAff: G2
  prj.affine(rAff, r)

  return rAff

#-------------------------------------------------------------------------------

#[
type InputTuple = tuple[idx:int, coeffs: openArray[Fr] , points: openArray[G1]]

func msmMultiThreadedG1*( coeffs: openArray[Fr] , points: openArray[G1] ): G1 =
  let N = coeffs.len
  assert( N == points.len, "incompatible sequence lengths" )

  let nthreadsTarget = 8

  # for N <= 255 , we use 1 thread
  # for N == 256 , we use 2 threads
  # for N == 512 , we use 4 threads 
  # for N >= 1024, we use 8 threads 
  let nthreads = max( 1 , min( N div 128 , nthreadsTarget ) )

  let m = N div nthreads

  var threads : seq[Thread[InputTuple]] = newSeq[Thread[InputTuple]]( nthreads )
  var results : seq[G1]                 = newSeq[G1]( nthreads )

  proc myThreadFunc( inp: InputTuple ) {.thread.} =
    results[inp.idx] = msmConstantineG1( inp.coeffs, inp.points )

  for i in 0..<nthreads:
    let a = i*m
    let b = if (i == nthreads-1): N else: (i+1)*m
    createThread(threads[i], myThreadFunc, (i, coeffs[a..<b], points[a..<b]))

  joinThreads(threads)

  var r : G1 = infG1
  for i in 0..<nthreads: r += results[i]

  return r
]#

#-------------------------------------------------------------------------------

func msmNaiveG1*( coeffs: seq[Fr] , points: seq[G1] ): G1 =
  let N = coeffs.len
  assert( N == points.len, "incompatible sequence lengths" )

  var s : ProjG1
  s.setInf()

  for i in 0..<N:
    var t : ProjG1
    prj.fromAffine( t, points[i] )
    scl.scalarMul_vartime( t , coeffs[i].toBig() )
    s += t

  var r : G1
  prj.affine( r, s )

  return r

#---------------------------------------

func msmNaiveG2*( coeffs: seq[Fr] , points: seq[G2] ): G2 =
  let N = coeffs.len
  assert( N == points.len, "incompatible sequence lengths" )

  var s : ProjG2
  s.setInf()

  for i in 0..<N:
    var t : ProjG2
    prj.fromAffine( t, points[i] )
    scl.scalarMul_vartime( t , coeffs[i].toBig() )
    s += t

  var r : G2
  prj.affine( r, s)

  return r

#-------------------------------------------------------------------------------

func msmG1*( coeffs: seq[Fr] , points: seq[G1] ): G1 = msmConstantineG1(coeffs, points)
func msmG2*( coeffs: seq[Fr] , points: seq[G2] ): G2 = msmConstantineG2(coeffs, points)

#-------------------------------------------------------------------------------

