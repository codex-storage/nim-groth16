
#
# univariate polynomials over Fr
#
# constantine's implementation is "somewhat lacking", so we have to
# implement these ourselves...
#
# TODO: more efficient implementations (right now I just want something working)
#

import std/sequtils
import std/sugar

import constantine/math/arithmetic except Fp,Fr
import constantine/math/io/io_fields

import bn128
import domain
import ntt

#-------------------------------------------------------------------------------

type 
  Poly* = object
    coeffs* : seq[Fr]

#-------------------------------------------------------------------------------

func polyDegree*(P: Poly) : int =
  let xs = P.coeffs ; let n = xs.len
  var d : int = n-1
  while isZeroFr(xs[d]) and (d >= 0): d -= 1
  return d

func polyIsZero*(P: Poly) : bool = 
  let xs = P.coeffs ; let n = xs.len
  var b = true
  for i in 0..<n:
    if not isZeroFr(xs[i]):
      b = false
      break
  return b

func polyIsEqual*(P, Q: Poly) : bool = 
  let xs : seq[Fr] = P.coeffs ; let n = xs.len
  let ys : seq[Fr] = Q.coeffs ; let m = ys.len
  var b = true
  if n >= m:
    for i in 0..<m: ( if not isEqualFr(xs[i], ys[i]): ( b = false ; break ) )
    for i in m..<n: ( if not isZeroFr( xs[i]       ): ( b = false ; break ) )
  else:
    for i in 0..<n: ( if not isEqualFr(xs[i], ys[i]): ( b = false ; break ) )
    for i in n..<m: ( if not isZeroFr(        ys[i]): ( b = false ; break ) )
  return b

#-------------------------------------------------------------------------------

func polyEvalAt*(P: Poly, x0: Fr): Fr =
  let cs = P.coeffs ; let n = cs.len
  var y : Fr = zeroFr
  var r : Fr = oneFr
  if n > 0: y = cs[0]
  for i in 1..<n:
    r *= x0
    y += cs[i] * r
  return y

#-------------------------------------------------------------------------------

func polyNeg*(P: Poly) : Poly =
  let zs : seq[Fr] = map( P.coeffs , negFr )
  return Poly(coeffs: zs)

func polyAdd*(P, Q: Poly) : Poly =
  let xs = P.coeffs ; let n = xs.len
  let ys = Q.coeffs ; let m = ys.len
  var zs : seq[Fr]
  if n >= m:
    for i in 0..<m: zs.add( xs[i] + ys[i] )
    for i in m..<n: zs.add( xs[i]         )
  else:
    for i in 0..<n: zs.add( xs[i] + ys[i] )
    for i in n..<m: zs.add(         ys[i] )
  return Poly(coeffs: zs)

func polySub*(P, Q: Poly) : Poly =
  let xs = P.coeffs ; let n = xs.len
  let ys = Q.coeffs ; let m = ys.len
  var zs : seq[Fr]
  if n >= m:
    for i in 0..<m: zs.add( xs[i]  - ys[i] )
    for i in m..<n: zs.add( xs[i]          )
  else:
    for i in 0..<n: zs.add( xs[i]  + ys[i] )
    for i in n..<m: zs.add( zeroFr - ys[i] )
  return Poly(coeffs: zs)

#-------------------------------------------------------------------------------

func polyScale*(s: Fr, P: Poly): Poly =
  let zs : seq[Fr] = map( P.coeffs , proc (x: Fr): Fr = s*x )
  return Poly(coeffs: zs)

#-------------------------------------------------------------------------------

func polyMulNaive*(P, Q : Poly): Poly =
  let xs = P.coeffs ; let n1 = xs.len
  let ys = Q.coeffs ; let n2 = ys.len
  let N  = n1 + n2 - 1
  var zs : seq[Fr] = newSeq[Fr](N) 
  for k in 0..<N:
    # 0 <= i <= min(k , n1-1)
    # 0 <= j <= min(k , n2-1)
    # k = i + j
    # 0 >= i = k - j >= k - min(k , n2-1)
    # 0 >= j = k - i >= k - min(k , n1-1)   
    let A : int = max( 0 , k - min(k , n2-1) )
    let B : int = min( k , n1-1 )
    zs[k] = zeroFr
    for i in A..B:
      let j = k-i
      zs[k] += xs[i] * ys[j]
  return Poly(coeffs: zs)

func polyMul*(P, Q : Poly): Poly =
  return polyMulNaive(P, Q)   

#-------------------------------------------------------------------------------

func `==`*(P, Q: Poly): bool = return polyIsEqual(P, Q)

func `+`*(P, Q: Poly): Poly  = return polyAdd(P, Q)
func `-`*(P, Q: Poly): Poly  = return polySub(P, Q)
func `*`*(P, Q: Poly): Poly  = return polyMul(P, Q)

func `*`*(s: Fr  , P: Poly): Poly  = return polyScale(s, P)
func `*`*(P: Poly, s: Fr  ): Poly  = return polyScale(s, P)

#-------------------------------------------------------------------------------

# the vanishing polynomial `(x^N - 1)`
func vanishingPoly*(N: int): Poly = 
  assert( N>=1 )
  var cs : seq[Fr] = newSeq[Fr]( N+1 )
  cs[0] = negFr( oneFr )
  cs[N] = oneFr
  return Poly(coeffs: cs)

type
  QuotRem*[T] = object
    quot* : T 
    rem*  : T 

# divide by the vanishing polynomial `(x^N - 1)`
# returns the quotient and remainder
func polyQuotRemByVanishing*(P: Poly, N: int): QuotRem[Poly] = 
  assert( N>=1 )
  let deg  : int     = polyDegree(P)
  let src  : seq[Fr] = P.coeffs 
  var quot : seq[Fr] = newSeq[Fr]( max(1, deg - N + 1) )
  var rem  : seq[Fr] = newSeq[Fr]( N )

  if deg < N:
    rem = src
  
  else:
    # compute quot
    for j in countdown(deg-N, 0):
      if j+N <= deg-N:
        quot[j] = src[j+N] + quot[j+N]
      else:
        quot[j] = src[j+N]
    # compute rem
    for j in 0..<N:
      if j <= deg-N:
        rem[j] = src[j] + quot[j]
      else:
        rem[j] = src[j]

  return QuotRem[Poly]( quot:Poly(coeffs:quot), rem:Poly(coeffs:rem) )

# divide by the vanishing polynomial `(x^N - 1)`
func polyDivideByVanishing*(P: Poly, N: int): Poly = 
  let qr = polyQuotRemByVanishing(P, N)
  assert( polyIsZero(qr.rem) )
  return qr.quot

#-------------------------------------------------------------------------------

# evaluates a polynomial on an FFT domain
func polyForwardNTT*(P: Poly, D: Domain): seq[Fr] =
  let n = P.coeffs.len
  assert( n <= D.domainSize , "the domain must be as least as big as the polynomial" )

  if n == D.domainSize:
    let src : seq[Fr] = P.coeffs
    return forwardNTT(src, D)
  else:
    var src : seq[Fr] = P.coeffs
    for i in n..<D.domainSize: src.add( zeroFr )
    return forwardNTT(src, D)

#---------------------------------------

# interpolates a polynomial on an FFT domain
func polyInverseNTT*(ys: seq[Fr], D: Domain): Poly =
  let n = ys.len
  assert( n == D.domainSize , "the domain must be same size as the input" )
  let tgt = inverseNTT(ys, D)
  return Poly(coeffs: tgt)

#-------------------------------------------------------------------------------

proc sanityCheckOneHalf*() =
  let two    = oneFr + oneFr
  let invTwo = oneHalfFr
  echo(toDecimalFr(two))
  echo(toDecimalFr(invTwo * two))
  echo(toHex(invTwo))

proc sanityCheckVanishing*() = 
  var js : seq[int] = toSeq(101..112)
  let cs : seq[Fr]  = map( js, intToFr )
  let P  : Poly     = Poly( coeffs:cs )

  echo("degree of P = ",polyDegree(P))
  debugPrintSeqFr("xs", P.coeffs)

  let n  : int = 5
  let QR = polyQuotRemByVanishing(P, n)
  let Q  = QR.quot
  let R  = QR.rem

  debugPrintSeqFr("Q", Q.coeffs)
  debugPrintSeqFr("R", R.coeffs)

  let Z : Poly = vanishingPoly(n)
  let S : Poly = Q * Z + R

  debugPrintSeqFr("zs", S.coeffs)
  echo( polyIsEqual(P,S) )

proc sanityCheckNTT*() = 
  var js : seq[int] = toSeq(101..108)
  let cs : seq[Fr]  = map( js, intToFr )
  let P  : Poly     = Poly( coeffs:cs )
  let D  : Domain   = createDomain(8)
  let xs : seq[Fr]  = D.enumerateDomain()
  let ys : seq[Fr]  = collect( newSeq, (for x in xs: polyEvalAt(P,x)) ) 
  let zs : seq[Fr]  = polyForwardNTT(P ,D)
  let Q  : Poly     = polyInverseNTT(zs,D)
  debugPrintSeqFr("xs", xs)
  debugPrintSeqFr("ys", ys)
  debugPrintSeqFr("zs", zs)
  debugPrintSeqFr("us", Q.coeffs)

#-------------------------------------------------------------------------------
