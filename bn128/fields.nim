
#
# the prime fields Fp and Fr with sizes
#
#   p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
#   r = 21888242871839275222246405745257275088548364400416034343698204186575808495617
#

import sugar

import std/bitops
import std/sequtils

import constantine/math/arithmetic
import constantine/math/io/io_fields
import constantine/math/io/io_bigints
import constantine/math/config/curves
import constantine/math/config/type_ff          as tff
import constantine/math/extension_fields/towers as ext

#-------------------------------------------------------------------------------

type B*    = BigInt[256]
type Fr*   = tff.Fr[BN254Snarks]
type Fp*   = tff.Fp[BN254Snarks]

type Fp2*  = ext.QuadraticExt[Fp]
type Fp12* = ext.Fp12[BN254Snarks]

func mkFp2* (i: Fp, u: Fp) : Fp2 =
  let c : array[2, Fp] = [i,u]
  return ext.QuadraticExt[Fp]( coords: c )

#-------------------------------------------------------------------------------

const primeP* : B = fromHex( B, "0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47", bigEndian )
const primeR* : B = fromHex( B, "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001", bigEndian )

#-------------------------------------------------------------------------------

const zeroFp*  : Fp = fromHex( Fp, "0x00" )
const zeroFr*  : Fr = fromHex( Fr, "0x00" )
const oneFp*   : Fp = fromHex( Fp, "0x01" )
const oneFr*   : Fr = fromHex( Fr, "0x01" )

const zeroFp2* : Fp2 = mkFp2( zeroFp, zeroFp )
const oneFp2*  : Fp2 = mkFp2( oneFp , zeroFp )

#-------------------------------------------------------------------------------

func intToB*(a: uint): B =
  var y : B
  y.setUint(a)
  return y

func intToFp*(a: int): Fp =
  var y : Fp
  y.fromInt(a)
  return y

func intToFr*(a: int): Fr =
  var y : Fr
  y.fromInt(a)
  return y

#-------------------------------------------------------------------------------

func isZeroFp* (x: Fp ): bool = bool(isZero(x))
func isZeroFp2*(x: Fp2): bool = bool(isZero(x))
func isZeroFr* (x: Fr ): bool = bool(isZero(x))

func isEqualFp* (x, y: Fp ): bool = bool(x == y)
func isEqualFp2*(x, y: Fp2): bool = bool(x == y)
func isEqualFr* (x, y: Fr ): bool = bool(x == y)

func `===`*(x, y: Fp ): bool = isEqualFp(x,y)
func `===`*(x, y: Fp2): bool = isEqualFp2(x,y)
func `===`*(x, y: Fr ): bool = isEqualFr(x,y)

#-------------------

func isEqualFpSeq*(xs, ys: seq[Fp]): bool =
  let n = xs.len
  assert( n == ys.len )
  var b = true
  for i in 0..<n:
    if not bool(xs[i] == ys[i]):
      b = false
      break
  return b

func isEqualFrSeq*(xs, ys: seq[Fr]): bool =
  let n = xs.len
  assert( n == ys.len )
  var b = true
  for i in 0..<n:
    if not bool(xs[i] == ys[i]):
      b = false
      break
  return b

func `===`*(xs, ys: seq[Fp]): bool = isEqualFpSeq(xs,ys)
func `===`*(xs, ys: seq[Fr]): bool = isEqualFrSeq(xs,ys)

#-------------------------------------------------------------------------------

func `+`*[n](x, y: BigInt[n] ): BigInt[n] = ( var z : BigInt[n] = x ; z += y ; return z )
func `+`*(x, y: Fp ): Fp  =  ( var z : Fp  = x ; z += y ; return z )
func `+`*(x, y: Fp2): Fp2 =  ( var z : Fp2 = x ; z += y ; return z )
func `+`*(x, y: Fr ): Fr  =  ( var z : Fr  = x ; z += y ; return z )

func `-`*[n](x, y: BigInt[n] ): BigInt[n] = ( var z : BigInt[n] = x ; z -= y ; return z )
func `-`*(x, y: Fp ): Fp  =  ( var z : Fp  = x ; z -= y ; return z )
func `-`*(x, y: Fp2): Fp2 =  ( var z : Fp2 = x ; z -= y ; return z )
func `-`*(x, y: Fr ): Fr  =  ( var z : Fr  = x ; z -= y ; return z )

func `*`*(x, y: Fp ): Fp  =  ( var z : Fp  = x ; z *= y ; return z )
func `*`*(x, y: Fp2): Fp2 =  ( var z : Fp2 = x ; z *= y ; return z )
func `*`*(x, y: Fr ): Fr  =  ( var z : Fr  = x ; z *= y ; return z )

func negFp* (y: Fp ): Fp  =  ( var z : Fp  = zeroFp  ; z -= y ; return z )
func negFp2*(y: Fp2): Fp2 =  ( var z : Fp2 = zeroFp2 ; z -= y ; return z )
func negFr* (y: Fr ): Fr  =  ( var z : Fr  = zeroFr  ; z -= y ; return z )

func invFp*(y: Fp): Fp =  ( var z : Fp = y ; inv(z) ; return z )
func invFr*(y: Fr): Fr =  ( var z : Fr = y ; inv(z) ; return z )

func squareFp* (y: Fp):  Fp  =  ( var z : Fp  = y ; square(z) ; return z )
func squareFp2*(y: Fp2): Fp2 =  ( var z : Fp2 = y ; square(z) ; return z )
func squareFr* (y: Fr):  Fr  =  ( var z : Fr  = y ; square(z) ; return z )

# template/generic instantiation of `pow_vartime` from here
# /Users/bkomuves/.nimble/pkgs/constantine-0.0.1/constantine/math/arithmetic/finite_fields.nim(389, 7) template/generic instantiation of `fieldMod` from here
# /Users/bkomuves/.nimble/pkgs/constantine-0.0.1/constantine/math/config/curves_prop_field_derived.nim(67, 5) Error: undeclared identifier: 'getCurveOrder'
# ...
func smallPowFr*(base: Fr, expo: uint): Fr =
  var a : Fr   = oneFr
  var s : Fr   = base
  var e : uint = expo
  while (e > 0):
    if bitand(e,1) > 0: a *= s
    e = (e shr 1)
    square(s)
  return a

func smallPowFr*(base: Fr, expo: int): Fr =
  if expo >= 0:
    return smallPowFr( base, uint(expo) )
  else:
    return smallPowFr( invFr(base) , uint(-expo) )

#-------------------------------------------------------------------------------

func deltaFr*(i, j: int) : Fr =
  return (if (i == j): oneFr else: zeroFr)

#-------------------------------------------------------------------------------

# Montgomery batch inversion
func batchInverseFr*( xs: seq[Fr] ) : seq[Fr] =
  let n = xs.len
  assert(n>0)
  var us : seq[Fr] = newSeq[Fr](n+1)
  var a = xs[0]
  us[0] = oneFr
  us[1] = a
  for i in 1..<n: ( a *= xs[i] ; us[i+1] = a )
  var vs : seq[Fr] = newSeq[Fr](n)
  vs[n-1] = invFr( us[n] )
  for i in countdown(n-2,0): vs[i] = vs[i+1] * xs[i+1]
  return collect( newSeq, (for i in 0..<n: us[i]*vs[i] ) )

proc sanityCheckBatchInverseFr*() =
  let xs : seq[Fr] = map( toSeq(101..137) , intToFr )
  let ys = batchInverseFr( xs )
  let zs = collect( newSeq, (for x in xs: invFr(x)) )
  let n = xs.len
  # for i in 0..<n: echo(i," | batch = ",toDecimalFr(ys[i])," | ref = ",toDecimalFr(zs[i]) )
  for i in 0..<n:
    if not bool(ys[i] == zs[i]):
      echo "batch inverse test FAILED!"
      return
  echo "batch iverse test OK."

#-------------------------------------------------------------------------------

