
#
# parsing the `.wtns` file computed by `circom` witness code genereators
#
# Note: the witness values are a flat array of size `nvars`, organized
# in the following order:
#
#     [ 1 | public output | public input | private input | secret witness ]
#
# so we have
#
#     nvars = 1 + pub + secret = 1 + npubout + npubin + nprivin + nsecret
#
# NOTE: Unlike the `.zkey` files, which encode field elements in the 
# Montgomery representation, the `.wtns` file encode field elements in 
# the standard representation!
#

import std/streams

import constantine/math/arithmetic except Fp, Fr
import constantine/math/io/io_bigints

import groth16/bn128
import groth16/files/container

#-------------------------------------------------------------------------------

type 
  Witness* = object
    curve*  : string
    r*      : BigInt[256] 
    nvars*  : int
    values* : seq[Fr]

#-------------------------------------------------------------------------------

proc parseSection1_header( stream: Stream, user: var Witness, sectionLen: int ) =
  # echo "\nparsing witness header"
  
  let (n8r, r) = parsePrimeField( stream )     # size of the scalar field
  user.r = r;

  # echo("r = ",toDecimalBig(r))

  assert( sectionLen == 4 + n8r + 4 , "unexpected section length")

  assert( n8r == 32         , "expecting 256 bit prime"        )
  assert( bool(r == primeR) , "expecting the alt-bn128 curve" )
  user.curve = "bn128"

  let nvars  = int( stream.readUint32() )
  user.nvars = nvars;

  # echo("nvars  = ",nvars)

#-------------------------------------------------------------------------------

proc parseSection2_witness( stream: Stream, user: var Witness, sectionLen: int )  =

  assert( sectionLen == 32 * user.nvars )
  user.values = loadValuesFrStd( user.nvars, stream )

#-------------------------------------------------------------------------------

proc wtnsCallback(stream: Stream, sectId: int, sectLen: int, user: var Witness) = 
  #echo(sectId)
  case sectId
    of 1: parseSection1_header(  stream, user, sectLen )
    of 2: parseSection2_witness( stream, user, sectLen )
    else: discard

proc parseWitness* (fname: string): Witness = 
  var wtns : Witness
  parseContainer( "wtns", 2, fname, wtns, wtnsCallback, proc (id: int): bool = id == 1 )
  parseContainer( "wtns", 2, fname, wtns, wtnsCallback, proc (id: int): bool = id != 1 )
  return wtns

#-------------------------------------------------------------------------------

