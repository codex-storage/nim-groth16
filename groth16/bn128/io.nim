

import std/strutils
import std/streams

import constantine/math/arithmetic    except Fp, Fp2, Fr
import constantine/math/io/io_fields  except Fp, Fp2, Fp
import constantine/math/io/io_bigints
import constantine/math/config/curves
import constantine/math/config/type_ff as tff except Fp, Fp2, Fr

import groth16/bn128/fields
import groth16/bn128/curves

#-------------------------------------------------------------------------------

const primeP_254 : BigInt[254] = fromHex( BigInt[254], "0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47", bigEndian )
const primeR_254 : BigInt[254] = fromHex( BigInt[254], "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001", bigEndian )

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

#---------------------------------------

const k65536 : BigInt[254] = fromHex( BigInt[254], "0x10000", bigEndian )

func signedToDecimalFp*(a : Fp): string =
  if bool( a.toBig() > primeP_254 - k65536 ):
    return "-" & toDecimalFp(negFp(a))
  else:
    return toDecimalFp(a)

func signedToDecimalFr*(a : Fr): string =
  if bool( a.toBig() > primeR_254 - k65536 ):
    return "-" & toDecimalFr(negFr(a))
  else:
    return toDecimalFr(a)

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

# the binary file `.zkey` used by the `circom` ecosystem uses little-endian 
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

func toMontgomeryFr*(x : Fr) : Fr =
  var y : Fr = x;
  y *= frMontR
  return y

#-------------------------------------------------------------------------------
# Unmarshalling field elements
# Note: in the `.zkey` coefficients, e apparently DOUBLE Montgomery encoding is used ?!?
#

func unmarshalFpMont* ( bs: array[32,byte] ) : Fp =
  var big : BigInt[254]
  unmarshal( big, bs, littleEndian );
  var x : Fp
  x.fromBig( big )
  return fromMontgomeryFp(x)

# WTF Jordi, go home you are drunk
func unmarshalFrWTF* ( bs: array[32,byte] ) : Fr =
  var big : BigInt[254]
  unmarshal( big, bs, littleEndian );
  var x : Fr
  x.fromBig( big )
  return fromMontgomeryFr(fromMontgomeryFr(x))

func unmarshalFrStd* ( bs: array[32,byte] ) : Fr =
  var big : BigInt[254]
  unmarshal( big, bs, littleEndian );
  var x : Fr
  x.fromBig( big )
  return x

func unmarshalFrMont* ( bs: array[32,byte] ) : Fr =
  var big : BigInt[254]
  unmarshal( big, bs, littleEndian );
  var x : Fr
  x.fromBig( big )
  return fromMontgomeryFr(x)

#-------------------------------------------------------------------------------

func unmarshalFpMontSeq* ( len: int,  bs: openArray[byte] ) : seq[Fp] =
  var vals  : seq[Fp] = newSeq[Fp]( len )
  var bytes : array[32,byte]
  for i in 0..<len:
    copyMem( addr(bytes) , unsafeAddr(bs[32*i]) , 32 )
    vals[i] = unmarshalFpMont( bytes )
  return vals

func unmarshalFrMontSeq* ( len: int,  bs: openArray[byte] ) : seq[Fr] =
  var vals  : seq[Fr] = newSeq[Fr]( len )
  var bytes : array[32,byte]
  for i in 0..<len:
    copyMem( addr(bytes) , unsafeAddr(bs[32*i]) , 32 )
    vals[i] = unmarshalFrMont( bytes )
  return vals

#-------------------------------------------------------------------------------

proc loadValueFrWTF*( stream: Stream ) : Fr =
  var bytes : array[32,byte]
  let n = stream.readData( addr(bytes), 32 )
  # for i in 0..<32: stdout.write(" " & toHex(bytes[i]))
  # echo("")
  assert( n == 32 )
  return unmarshalFrWTF(bytes)

proc loadValueFrStd*( stream: Stream ) : Fr =
  var bytes : array[32,byte]
  let n = stream.readData( addr(bytes), 32 )
  assert( n == 32 )
  return unmarshalFrStd(bytes)

proc loadValueFrMont*( stream: Stream ) : Fr =
  var bytes : array[32,byte]
  let n = stream.readData( addr(bytes), 32 )
  assert( n == 32 )
  return unmarshalFrMont(bytes)

proc loadValueFpMont*( stream: Stream ) : Fp =
  var bytes : array[32,byte]
  let n = stream.readData( addr(bytes), 32 )
  assert( n == 32 )
  return unmarshalFpMont(bytes)

proc loadValueFp2Mont*( stream: Stream ) : Fp2 =
  let i = loadValueFpMont( stream )
  let u = loadValueFpMont( stream )
  return mkFp2(i,u)

#---------------------------------------

proc loadValuesFrStd*( len: int, stream: Stream ) : seq[Fr] =
  var values : seq[Fr]
  for i in 1..len:
    values.add( loadValueFrStd(stream) )
  return values

proc loadValuesFpMont*( len: int, stream: Stream ) : seq[Fp] =
  var values : seq[Fp]
  for i in 1..len:
    values.add( loadValueFpMont(stream) )
  return values

proc loadValuesFrMont*( len: int, stream: Stream ) : seq[Fr] =
  var values : seq[Fr]
  for i in 1..len:
    values.add( loadValueFrMont(stream) )
  return values

#-------------------------------------------------------------------------------

proc loadPointG1*( stream: Stream ) : G1 =
  let x = loadValueFpMont( stream )
  let y = loadValueFpMont( stream )
  return mkG1(x,y)

proc loadPointG2*( stream: Stream ) : G2 =
  let x = loadValueFp2Mont( stream )
  let y = loadValueFp2Mont( stream )
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

