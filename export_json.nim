
#
# export proof and public input in `circom`-compatible JSON files
#

import constantine/math/arithmetic   except Fp, Fr
#import constantine/math/io/io_fields except Fp, Fr

import bn128
from ./groth16 import Proof

#-------------------------------------------------------------------------------

func toQuotedDecimalFp(x: Fp): string = 
  let s : string = toDecimalFp(x)
  return ("\"" & s & "\"")

func toQuotedDecimalFr(x: Fr): string = 
  let s : string = toDecimalFr(x)
  return ("\"" & s & "\"")

#-------------------------------------------------------------------------------

# exports the public input/output into as a JSON file
proc exportPublicIO*( fpath: string, prf: Proof ) = 

  # debugPrintFrSeq("public IO",prf.publicIO)

  let n : int = prf.publicIO.len 
  assert( n > 0  )
  assert( bool(prf.publicIO[0] == oneFr) )

  let f = open(fpath, fmWrite)
  defer: f.close()

  for i in 1..<n:
    let str : string = toQuotedDecimalFr( prf.publicIO[i] )
    if i==1:
      f.writeLine("[ " & str)
    else:
      f.writeLine(", " & str)
  f.writeLine("] ")

#-------------------------------------------------------------------------------

proc writeFp2( f: File, c: char, z: Fp2 ) =
  let prefix = "    " & c & " "
  let indent = "      "
  f.writeLine( prefix & "[ " & toQuotedDecimalFp( z.coords[0] ) )
  f.writeLine( indent & ", " & toQuotedDecimalFp( z.coords[1] ) )
  f.writeLine( indent & "]")

proc writeG1( f: File, p: G1 ) =
  f.writeLine("    [ " & toQuotedDecimalFp( p.x   ) )
  f.writeLine("    , " & toQuotedDecimalFp( p.y   ) )
  f.writeLine("    , " & toQuotedDecimalFp( oneFp ) )
  f.writeLine("    ]")

proc writeG2( f: File, p: G2 ) =
  writeFp2( f , '[' , p.x    )
  writeFp2( f , ',' , p.y    )
  writeFp2( f , ',' , oneFp2 )
  f.writeLine("    ]")

#-------------------------------------------------------------------------------

# exports the proof into as a JSON file
proc exportProof*( fpath: string, prf: Proof ) = 

  let f = open(fpath, fmWrite)
  defer: f.close()

  f.writeLine("{ \"protocol\": \"groth16\"")
  f.writeLine(", \"curve\":    \"bn128\""  )
  f.writeLine(", \"pi_a\":" ) ; writeG1( f, prf.pi_a )
  f.writeLine(", \"pi_b\":" ) ; writeG2( f, prf.pi_b )
  f.writeLine(", \"pi_c\":" ) ; writeG1( f, prf.pi_c )
  f.writeLine("}")

#-------------------------------------------------------------------------------

#[
#import std/sequtils

func getFakeProof*() : Proof = 
  let pub : seq[Fr] = map( [1,101,102,103,117,119] , intToFr )
  let p = unsafeMkG1( intToFp(666) , intToFp(777) )
  let r = unsafeMkG1( intToFp(888) , intToFp(999) )
  let x = mkFp2( intToFp(22) , intToFp(33) )
  let y = mkFp2( intToFp(44) , intToFp(55) )
  let q = unsafeMkG2( x , y )
  return Proof( publicIO:pub, pi_a:p, pi_b:q, pi_c:r )

proc exportFakeProof*() = 
  let prf = getFakeProof()
  exportPublicIO( "fake_pub.json" , prf )
  exportProof(    "fake_prf.json" , prf )
]#

#-------------------------------------------------------------------------------
