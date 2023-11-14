
import std/random

# import constantine/platforms/abstractions

import constantine/math/arithmetic       except Fp, Fp2, Fr
import constantine/math/io/io_fields     except Fp, Fp2, Fr
import constantine/math/io/io_bigints

import ./fields

#-------------------------------------------------------------------------------
# random values

var randomInitialized : bool = false
var randomState       : Rand = initRand( 12345 )

proc rndUint64() : uint64 =
  return randomState.next()

proc initializeRandomIfNecessary() =
  if not randomInitialized:
    randomState = initRand()
    randomInitialized = true

#----------------------------|  01234567890abcdf01234567890abcdf01234567890abcdf01234567890abcdf
const m64  : B = fromHex( B, "0x0000000000000000000000000000000000000000000000010000000000000000", bigEndian )
const m128 : B = fromHex( B, "0x0000000000000000000000000000000100000000000000000000000000000000", bigEndian )
const m192 : B = fromHex( B, "0x0000000000000001000000000000000000000000000000000000000000000000", bigEndian )
#----------------------------|  01234567890abcdf01234567890abcdf01234567890abcdf01234567890abcdf

proc randBig*[bits: static int](): BigInt[bits] =

  initializeRandomIfNecessary()

  let a0 : uint64 = rndUint64()
  let a1 : uint64 = rndUint64()
  let a2 : uint64 = rndUint64()
  let a3 : uint64 = rndUint64()

  # echo((a0,a1,a2,a3))

  var b0 : BigInt[bits] ; b0.fromUint(a0)
  var b1 : BigInt[bits] ; b1.fromUint(a1)
  var b2 : BigInt[bits] ; b2.fromUint(a2)
  var b3 : BigInt[bits] ; b3.fromUint(a3)

  # constantine doesn't appear to have left shift....
  var c1,c2,c3 : BigInt[bits]
  prod( c1 , b1 , m64  )
  prod( c2 , b2 , m128 )
  prod( c3 , b3 , m192 )

  var d : BigInt[bits]
  d =  b0
  d += c1
  d += c2
  d += c3

  return d

proc randFr*(): Fr =
  let b : BigInt[254] = randBig[254]()
  var y : Fr
  y.fromBig( b )
  return y

proc testRandom*() =
  for i in 1..20:
    let x = randFr()
    echo(x.toHex())
  echo("-------------------")
  echo(primeR.toHex())

#-------------------------------------------------------------------------------

