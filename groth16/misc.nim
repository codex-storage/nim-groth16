
#
# miscellaneous routines
#

import strformat
import times, os, strutils

#-------------------------------------------------------------------------------

func seconds*(x: float): string = fmt"{x:.4f} seconds"

func quoted*(s: string): string = fmt"`{s:s}`"

#-------------------------------------------------------------------------------

template withMeasureTime*(doPrint: bool, text: string, code: untyped) =
  block:
    if doPrint:
      let t0 = epochTime()
      code
      let elapsed = epochTime() - t0
      let elapsedStr = elapsed.formatFloat(format = ffDecimal, precision = 4)
      echo ( text & " took " & elapsedStr & " seconds" )
    else:
      code

#-------------------------------------------------------------------------------

func delta*(i, j: int) : int =
  return (if (i == j): 1 else: 0)

#-------------------------------------------------------------------------------

func floorLog2* (x : int) : int = 
  var k = -1
  var y = x
  while (y > 0):
    k += 1
    y = y shr 1
  return k

func ceilingLog2* (x : int) : int = 
  if (x==0):
    return -1
  else:
    return (floorLog2(x-1) + 1)

#-------------------

#[
import std/math

proc sanityCheckLog2* () =
  for i in 0..18:
    let x = float64(i)
    echo( i," | ",floorLog2(i),"=",floor(log2(x))," | ",ceilingLog2(i),"=",ceil(log2(x)) )
]#

#-------------------------------------------------------------------------------

#[
func rotateSeq[T](xs: seq[T], ofs: int): seq[T] =
  let n = xs.len
  var ys : seq[T]
  for i in (0..<n):
    ys.add( xs[ (i+n+ofs) mod n ] )
  return ys
]#

#-------------------------------------------------------------------------------
