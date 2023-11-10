
#
# power-of-two sized multiplicative FFT domains in the scalar field
#

import constantine/math/io/io_bigints
import constantine/math/arithmetic   except Fp,Fr
import constantine/math/io/io_fields except Fp,Fr

import ./bn128
import ./misc

#-------------------------------------------------------------------------------

type 
  Domain* = object
    domainSize*    : int
    logDomainSize* : int
    domainGen*     : Fr

#-------------------------------------------------------------------------------

# the generator of the multiplicative subgroup with size `2^28`
const gen28 : Fr = fromHex( Fr, "0x2a3c09f0a58a7e8500e0a7eb8ef62abc402d111e41112ed49bd61b6e725b19f0" )

func createDomain*(size: int): Domain = 
  let log2 = ceilingLog2(size)
  assert( (1 shl log2) == size , "domain must have a power-of-two size" )

  let expo : uint = 1'u shl (28 - log2)
  let gen  : Fr   = smallPowFr(gen28, expo)

  let halfSize = size div 2
  let a : Fr = smallPowFr(gen, uint(size    ))
  let b : Fr = smallPowFr(gen, uint(halfSize))
  assert(     bool(a == oneFr) , "domain generator sanity check /A" )
  assert( not bool(b == oneFr) , "domain generator sanity check /B" )

  return Domain( domainSize:size, logDomainSize:log2, domainGen:gen )

#-------------------------------------------------------------------------------

func enumerateDomain*(D: Domain): seq[Fr] =
  var xs : seq[Fr] = newSeq[Fr](D.domainSize)
  var g  : Fr = oneFr
  for i in 0..<D.domainSize:
    xs[i] = g
    g *= D.domainGen
  return xs

#-------------------------------------------------------------------------------
