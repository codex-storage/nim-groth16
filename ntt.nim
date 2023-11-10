
#
# Number-theoretic transform
#

import std/sequtils

import constantine/math/arithmetic except Fp,Fr
import constantine/math/io/io_fields

import bn128
import domain

#-------------------------------------------------------------------------------

func forwardNTT_worker( m: int
                      , srcStride: int
                      , gen: Fr
                      , src: seq[Fr]     , srcOfs: int
                      , buf: var seq[Fr] , bufOfs: int
                      , tgt: var seq[Fr] , tgtOfs: int ) =
  case m 

    of 0: 
      tgt[tgtOfs] = src[srcOfs]
  
    of 1:
      tgt[tgtOfs  ] = src[srcOfs] + src[srcOfs+srcStride]
      tgt[tgtOfs+1] = src[srcOfs] - src[srcOfs+srcStride]

    else:
      let N     : int =  1 shl  m  
      let halfN : int =  1 shl (m-1)  
      var gpow  : Fr = gen
      square(gpow)
      forwardNTT_worker( m-1
                       , srcStride shl 1
                       , gpow
                       , src , srcOfs
                       , buf , bufOfs + N
                       , buf , bufOfs )
      forwardNTT_worker( m-1
                       , srcStride shl 1
                       , gpow
                       , src , srcOfs + srcStride
                       , buf , bufOfs + N
                       , buf , bufOfs + halfN )
      gpow = oneFr
      for j in 0..<halfN:
        let y : Fr = gpow * buf[bufOfs+j+halfN] 
        tgt[tgtOfs+j      ] = buf[bufOfs+j] + y
        tgt[tgtOfs+j+halfN] = buf[bufOfs+j] - y
        gpow *= gen

#---------------------------------------

# forward number-theoretical transform (corresponds to polynomial evaluation)
func forwardNTT*(src: seq[Fr], D: Domain): seq[Fr] =
  assert( D.domainSize == (1 shl D.logDomainSize) , "domain must have a power-of-two size" )
  assert( D.domainSize == src.len , "input must have the same size as the domain" )
  var buf : seq[Fr] = newSeq[Fr]( 2 * D.domainSize )
  var tgt : seq[Fr] = newSeq[Fr](     D.domainSize )
  forwardNTT_worker( D.logDomainSize
                   , 1
                   , D.domainGen
                   , src , 0
                   , buf , 0
                   , tgt , 0 )
  return tgt

#-------------------------------------------------------------------------------

const oneHalfFr* : Fr = fromHex(Fr, "0x183227397098d014dc2822db40c0ac2e9419f4243cdcb848a1f0fac9f8000001")

func inverseNTT_worker( m: int
                      , tgtStride: int
                      , gen: Fr
                      , src: seq[Fr]     , srcOfs: int
                      , buf: var seq[Fr] , bufOfs: int
                      , tgt: var seq[Fr] , tgtOfs: int ) =
  case m 

    of 0: 
      tgt[tgtOfs] = src[srcOfs]
  
    of 1:
      tgt[tgtOfs          ] = ( src[srcOfs] + src[srcOfs+1] ) * oneHalfFr
      tgt[tgtOfs+tgtStride] = ( src[srcOfs] - src[srcOfs+1] ) * oneHalfFr

    else:
      let N     : int =  1 shl  m  
      let halfN : int =  1 shl (m-1)  
      let ginv  : Fr = invFr(gen)
      var gpow  : Fr = oneHalfFr

      for j in 0..<halfN:
        buf[bufOfs+j      ] = ( src[srcOfs+j] + src[srcOfs+j+halfN] ) * oneHalfFr
        buf[bufOfs+j+halfN] = ( src[srcOfs+j] - src[srcOfs+j+halfN] ) * gpow
        gpow *= ginv

      gpow = gen
      square(gpow)

      inverseNTT_worker( m-1
                       , tgtStride shl 1
                       , gpow
                       , buf , bufOfs
                       , buf , bufOfs + N
                       , tgt , tgtOfs )
      inverseNTT_worker( m-1
                       , tgtStride shl 1
                       , gpow
                       , buf , bufOfs + halfN
                       , buf , bufOfs + N
                       , tgt , tgtOfs + tgtStride )

#---------------------------------------

# inverse number-theoretical transform (corresponds to polynomial interpolation)
func inverseNTT*(src: seq[Fr], D: Domain): seq[Fr] =
  assert( D.domainSize == (1 shl D.logDomainSize) , "domain must have a power-of-two size" )
  assert( D.domainSize == src.len , "input must have the same size as the domain" )
  var buf : seq[Fr] = newSeq[Fr]( 2 * D.domainSize )
  var tgt : seq[Fr] = newSeq[Fr](     D.domainSize )
  inverseNTT_worker( D.logDomainSize
                   , 1
                   , D.domainGen
                   , src , 0
                   , buf , 0
                   , tgt , 0 )
  return tgt

#-------------------------------------------------------------------------------
