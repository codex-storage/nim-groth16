
import std/strutils
import std/streams

import constantine/math/arithmetic
import constantine/math/io/io_fields
import constantine/math/io/io_bigints
import constantine/math/config/curves 
import constantine/math/config/type_ff as tff

import constantine/math/extension_fields/towers             as ext
import constantine/math/elliptic/ec_shortweierstrass_affine as ell

#-------------------------------------------------------------------------------

type B*   = BigInt[256]
type Fr*  = tff.Fr[BN254Snarks]
type Fp*  = tff.Fp[BN254Snarks]
type Fp2* = ext.QuadraticExt[Fp]
type G1*  = ell.ECP_ShortW_Aff[Fp , ell.G1]
type G2*  = ell.ECP_ShortW_Aff[Fp2, ell.G2]

func mkFp2(i: Fp, u: Fp) : Fp2 =
  let c : array[2, Fp] = [i,u]
  return ext.QuadraticExt[Fp]( coords: c )

func unsafeMkG1( X, Y: Fp ) : G1 = 
  return ell.ECP_ShortW_Aff[Fp, ell.G1](x: X, y: Y)

func unsafeMkG2( X, Y: Fp2 ) : G2 = 
  return ell.ECP_ShortW_Aff[Fp2, ell.G2](x: X, y: Y)

#-------------------------------------------------------------------------------

const primeP* : B = fromHex( B, "0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47", bigEndian )
const primeR* : B = fromHex( B, "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001", bigEndian )

#-------------------------------------------------------------------------------

const zeroFp* : Fp = fromHex( Fp, "0x00" )
const zeroFr* : Fr = fromHex( Fr, "0x00" )
const oneFp*  : Fp = fromHex( Fp, "0x01" )
const oneFr*  : Fr = fromHex( Fr, "0x01" )

const zeroFp2* : Fp2 = mkFp2( zeroFp, zeroFp )
const infG1*   : G1  = unsafeMkG1( zeroFp  , zeroFp  )
const infG2*   : G2  = unsafeMkG2( zeroFp2 , zeroFp2 )

#-------------------------------------------------------------------------------

func intToFp*(a: int) : Fp =
  var y : Fp
  y.fromInt(a)
  return y

func intToFr*(a: int) : Fr =
  var y : Fr
  y.fromInt(a)
  return y

#-------------------------------------------------------------------------------

func toDecimalBig*[n](a : BigInt[n]): string =
  var s : string = toDecimal(a)
  s = s.strip( leading=true, trailing=false, chars={'0'} )
  if s.len == 0: s="0"
  return s

func toDecimalFp*(a : Fp): string =
  var s : string = toDecimal(a)
  s = s.strip( leading=true, trailing=false, chars={'0'} )
  if s.len == 0: s="0"
  return s

func toDecimalFr*(a : Fr): string =
  var s : string = toDecimal(a)
  s = s.strip( leading=true, trailing=false, chars={'0'} )
  if s.len == 0: s="0"
  return s

#-------------------------------------------------------------------------------

func checkCurveEqG1*( x, y: Fp ) : bool =
  var x2 : Fp = x  ; square(x2);
  var y2 : Fp = y  ; square(y2);
  var x3 : Fp = x2 ; x3 *= x;
  var eq : Fp
  eq =  x3
  eq += intToFp(3)
  eq -= y2
  # echo("eq = ",toDecimalFp(eq))
  return (bool(isZero(eq)))

# y^2 = x^3 + B
# B = b1 + bu*u
# b1 = 19485874751759354771024239261021720505790618469301721065564631296452457478373 
# b2 = 266929791119991161246907387137283842545076965332900288569378510910307636690
const twistCoeffB_1 : Fp  = fromHex(Fp, "0x2b149d40ceb8aaae81be18991be06ac3b5b4c5e559dbefa33267e6dc24a138e5")
const twistCoeffB_u : Fp  = fromHex(Fp, "0x009713b03af0fed4cd2cafadeed8fdf4a74fa084e52d1852e4a2bd0685c315d2")
const twistCoeffB   : Fp2 = mkFp2( twistCoeffB_1 , twistCoeffB_u )

func checkCurveEqG2*( x, y: Fp2 ) : bool =
  var x2 : Fp2 = x  ; square(x2);
  var y2 : Fp2 = y  ; square(y2);
  var x3 : Fp2 = x2 ; x3 *= x;
  var eq : Fp2
  eq =  x3
  eq += twistCoeffB
  eq -= y2
  return (bool(isZero(eq)))

#-------------------------------------------------------------------------------

func mkG1( x, y: Fp ) : G1 = 
  if bool(isZero(x)) and bool(isZero(y)):
    return infG1
  else:
    assert( checkCurveEqG1(x,y) , "mkG1: not a G1 curve point" )
    return unsafeMkG1(x,y)

func mkG2( x, y: Fp2 ) : G2 = 
  if bool(isZero(x)) and bool(isZero(y)):
    return infG2
  else:
    assert( checkCurveEqG2(x,y) , "mkG2: not a G2 curve point" )
    return unsafeMkG2(x,y)

#-------------------------------------------------------------------------------
# Dealing with Montgomery representation
#

# R=2^256; this computes 2^256 mod Fp
func calcFpMontR*() : Fp = 
  var x : Fp = intToFp(2)
  for i in 1..8: 
    square(x)
  return x

# R=2^256; this computes the inverse of (2^256 mod Fp)
func calcFpInvMontR*() : Fp = 
  var x : Fp = calcFpMontR()
  inv(x)
  return x

# R=2^256; this computes 2^256 mod Fr
func calcFrMontR*() : Fr = 
  var x : Fr = intToFr(2)
  for i in 1..8: 
    square(x)
  return x

# R=2^256; this computes the inverse of (2^256 mod Fp)
func calcFrInvMontR*() : Fr = 
  var x : Fr = calcFrMontR()
  inv(x)
  return x

# apparently we cannot compute these in compile time for some reason or other... (maybe because `intToFp()`?)
const fpMontR*    : Fp = fromHex( Fp, "0x0e0a77c19a07df2f666ea36f7879462c0a78eb28f5c70b3dd35d438dc58f0d9d" )
const fpInvMontR* : Fp = fromHex( Fp, "0x2e67157159e5c639cf63e9cfb74492d9eb2022850278edf8ed84884a014afa37" )

# apparently we cannot compute these in compile time for some reason or other... (maybe because `intToFp()`?)
const frMontR*    : Fr = fromHex( Fr, "0x0e0a77c19a07df2f666ea36f7879462e36fc76959f60cd29ac96341c4ffffffb" )
const frInvMontR* : Fr = fromHex( Fr, "0x15ebf95182c5551cc8260de4aeb85d5d090ef5a9e111ec87dc5ba0056db1194e" )

proc checkMontgomeryConstants*() =
  assert( bool( fpMontR    == calcFpMontR()    ) )
  assert( bool( frMontR    == calcFrMontR()    ) )
  assert( bool( fpInvMontR == calcFpInvMontR() ) )
  assert( bool( frInvMontR == calcFrInvMontR() ) )
  echo("OK")

#---------------------------------------

# the binary files used by the `circom` ecosystem always use little-endian 
# Montgomery representation. So when we unmarshal with Constantine, it will
# give the wrong result. Calling this function on the result fixes that.
func fromMontgomeryFp*(x : Fp) : Fp = 
  var y : Fp = x;
  y *= fpInvMontR
  return y

func fromMontgomeryFr*(x : Fr) : Fr = 
  var y : Fr = x;
  y *= frInvMontR
  return y

#-------------------------------------------------------------------------------
# Unmarshalling field elements
# (note: circom binary files use little-endian Montgomery representation)
#

func unmarshalFp* ( bs: array[32,byte] ) : Fp = 
  var big : BigInt[254] 
  unmarshal( big, bs, littleEndian );  
  var x : Fp
  x.fromBig( big )
  return fromMontgomeryFp(x)

func unmarshalFr* ( bs: array[32,byte] ) : Fr = 
  var big : BigInt[254] 
  unmarshal( big, bs, littleEndian );  
  var x : Fr
  x.fromBig( big )
  return fromMontgomeryFr(x)

#-------------------------------------------------------------------------------

func unmarshalFpSeq* ( len: int,  bs: openArray[byte] ) : seq[Fp] = 
  var vals  : seq[Fp] = newSeq[Fp]( len )
  var bytes : array[32,byte]
  for i in 0..<len:
    copyMem( addr(bytes) , unsafeAddr(bs[32*i]) , 32 )
    vals[i] = unmarshalFp( bytes )
  return vals

func unmarshalFrSeq* ( len: int,  bs: openArray[byte] ) : seq[Fr] = 
  var vals  : seq[Fr] = newSeq[Fr]( len )
  var bytes : array[32,byte]
  for i in 0..<len:
    copyMem( addr(bytes) , unsafeAddr(bs[32*i]) , 32 )
    vals[i] = unmarshalFr( bytes )
  return vals

#-------------------------------------------------------------------------------

proc loadValueFp*( stream: Stream ) : Fp = 
  var bytes : array[32,byte]
  let n = stream.readData( addr(bytes), 32 )
  assert( n == 32 )
  return unmarshalFp(bytes)

proc loadValueFr*( stream: Stream ) : Fr = 
  var bytes : array[32,byte]
  let n = stream.readData( addr(bytes), 32 )
  assert( n == 32 )
  return unmarshalFr(bytes)

proc loadValueFp2*( stream: Stream ) : Fp2 = 
  let i = loadValueFp( stream )
  let u = loadValueFp( stream )
  return mkFp2(i,u)

#---------------------------------------

proc loadValuesFp*( len: int, stream: Stream ) : seq[Fp] = 
  var values : seq[Fp]
  for i in 1..len:
    values.add( loadValueFp(stream) )
  return values

proc loadValuesFr*( len: int, stream: Stream ) : seq[Fr] = 
  var values : seq[Fr]
  for i in 1..len:
    values.add( loadValueFr(stream) )
  return values

#-------------------------------------------------------------------------------

proc loadPointG1*( stream: Stream ) : G1 = 
  let x = loadValueFp( stream )
  let y = loadValueFp( stream )
  return mkG1(x,y)

proc loadPointG2*( stream: Stream ) : G2 = 
  let x = loadValueFp2( stream )
  let y = loadValueFp2( stream )
  return mkG2(x,y)

#---------------------------------------

proc loadPointsG1*( len: int, stream: Stream ) : seq[G1] = 
  var points : seq[G1]
  for i in 1..len:
    points.add( loadPointG1(stream) )
  return points

proc loadPointsG2*( len: int, stream: Stream ) : seq[G2] = 
  var points : seq[G2]
  for i in 1..len:
    points.add( loadPointG2(stream) )
  return points

#-------------------------------------------------------------------------------
