
#
# parsing the `.zkey` file format used by the `circom` ecosystem.
# this contains the prover and verifier keys.
#
# file format
# ===========
# 
# standard iden3 binary container format.
# field elements are in Montgomery representation, except for the coefficients
# which for some reason are double Montgomery encoded... (and unlike the 
# `.wtns` and `.r1cs` files which use the standard representation)
# 
# sections:
#
# 1: Header
# ---------
#   prover_type : word32 (Groth16 = 0x0001)
#
# 2: Groth16-specific header
# --------------------------
#   n8p     : word32    = how many bytes are a field element in Fp
#   p       : n8p bytes = the size of the prime field Fp (the base field)
#   n8r     : word32    = how many bytes are a field element in Fr
#   r       : n8p bytes = the size of the prime field Fr (the scalar field)
#   nvars   : word32    = number of witness variables
#   npub    : word32    = number of public variables (public input/output)
#   domSize : word32    = domain size (power of two)
#   alpha1  : G1        = [alpha]_1
#   beta1   : G1        = [beta]_1
#   beta2   : G2        = [beta]_2
#   gamma2  : G2        = [gamma]_2
#   delta1  : G1        = [delta]_1
#   delta2  : G2        = [delta_2]
#
# 3: IC
# -----
#   the curve points (corresponding to public input) required by the verifier
#   length = 2 * n8p * (npub + 1) = (npub+1) G1 points
#
# 4: Coeffs
# ---------
#   ncoeffs : words32 = number of entries
#   The nonzero coefficients in the A,B R1CS matrices (that is, sparse representation)
#   Remark: since we now that (A*witness).(B*witness) = C.witness
#   (12+n8r) bytes per entry:
#     m     : word32         = which matrix (0=A, 1=B)
#     c     : word32         = which row, from 0..domSize-1
#     s     : word32         = which column, from 0..nvars-1
#     value : Fr (n8r bytes)
#
#   for each such entry, we add `value * witness[c]` to the `i`-th element of
#   the corresponding column vector (meaning `A*witness` and `B*witness), then
#   compute (C*witness)[i] = (A*witness)[i] * (B*witness)[i]
#   These 3 column vectors is all we need in the proof generation.
#
#   WARNING! It appears that the values here are *doubly Montgomery encoded* (??!)
#
# 5: PointsA
# ----------
#   the curve points [A_j(tau)]_1 in G1
#   length = 2 * n8p * nvars = nvars G1 points
#
# 6: PointsB1
# -----------
#   the curve points [B_j(tau)]_1 in G1
#   length = 2 * n8p * nvars = nvars G1 points
#
# 7: PointsB2
# -----------
#   the curve points [B_j(tau)]_2 in G2
#   length = 4 * n8p * nvars = nvars G2 points
#
# 8: PointsC
# ----------
#   the curve points [ delta^-1 * ( beta*A_j(tau) + alpha*B_j(tau) + C_j(tau) ) ]_1 in G1
#   length = 2 * n8p * (nvars - npub - 1) = (nvars-npub-1) G1 points
#
# 9: PointsH
# ----------
#   what normally should be the curve points `[ delta^-1 * tau^i * Z(tau) ]_1`
#   HOWEVER, in the snarkjs implementation, they are different; namely
#   `[ delta^-1 * L_{2i+1} (tau) ]_1` where L_k are Lagrange polynomials
#   on the refined (double sized) domain 
#   See <https://geometry.xyz/notebook/the-hidden-little-secret-in-snarkjs>
#   length = 2 * n8p * domSize = domSize G1 points
#
# 10: Contributions
# -----
#   ??? (but not required for proving, only for checking that the `.zkey` file is valid)
#

#-------------------------------------------------------------------------------

import std/streams

import constantine/math/arithmetic except Fp, Fr
#import constantine/math/io/io_bigints
 
import ./bn128
import ./zkey_types
import ./container
import ./misc

#-------------------------------------------------------------------------------

proc parseSection1_proverType ( stream: Stream, user: var Zkey, sectionLen: int ) = 
  assert( sectionLen == 4 , "unexpected section length" )  
  let proverType = stream.readUint32
  assert( proverType == 1 , "expecting `.zkey` file for a Groth16 prover")

#-------------------------------------------------------------------------------

proc parseSection2_GrothHeader( stream: Stream, user: var ZKey, sectionLen: int ) =
  # echo "\nparsing the Groth16 zkey header"

  let (n8p, p) = parsePrimeField( stream )     # size of the base field
  let (n8r, r) = parsePrimeField( stream )     # size of the scalar field

  # echo("p = ",toDecimalBig(p))
  # echo("r = ",toDecimalBig(r))

  assert( sectionLen == 2*4 + n8p + n8r + 3*4 + 3*64 + 3*128 , "unexpected section length" )

  var header : GrothHeader
  header.p = p
  header.r = r

  header.flavour = Snarkjs

  assert( n8p == 32 , "expecting 256 bit primes")     
  assert( n8r == 32 , "expecting 256 bit primes")     

  assert( bool(p == primeP) , "expecting the alt-bn128 curve" )
  assert( bool(r == primeR) , "expecting the alt-bn128 curve" )
  header.curve = "bn128"

  let nvars   = int( stream.readUint32() )
  let npubs   = int( stream.readUint32() )
  let domsiz  = int( stream.readUint32() )
  let log2siz = ceilingLog2(domsiz)

  assert( (1 shl log2siz) == domsiz , "domain size should be a power of two" )

  # echo("nvars  = ",nvars)
  # echo("npubs  = ",npubs)
  # echo("domsiz = ",domsiz)

  header.nvars      = nvars
  header.npubs      = npubs
  header.domainSize = domsiz
  header.logDomainSize = log2siz

  user.header = header

  # 3 group elements in G1, 3 in G2
  var spec : SpecPoints
  spec.alpha1  = loadPointG1( stream )
  spec.beta1   = loadPointG1( stream )
  spec.beta2   = loadPointG2( stream )
  spec.gamma2  = loadPointG2( stream )
  spec.delta1  = loadPointG1( stream )
  spec.delta2  = loadPointG2( stream )
  spec.alphaBeta = pairing( spec.alpha1, spec.beta2 )
  user.specPoints = spec

#-------------------------------------------------------------------------------

proc parseSection4_Coeffs( stream: Stream, user: var ZKey, sectionLen: int ) =
  let ncoeffs = int( stream.readUint32() )
  assert( sectionLen == 4 + ncoeffs*(32+12) , "unexpected section length" )
  let nrows = user.header.domainSize
  let ncols = user.header.nvars
  
  var coeffs : seq[Coeff]
  for i in 1..ncoeffs:
    let m = int( stream.readUint32() )  # which matrix
    let r = int( stream.readUint32() )  # row (equation index)
    let c = int( stream.readUint32() )  # column (witness index)
    assert( m >= 0 and m <= 2 , "invalid matrix selector" )
    let sel : MatrixSel = case m
      of 0: MatrixA
      of 1: MatrixB
      of 2: MatrixC
      else: raise newException(AssertionDefect, "fatal error")
    assert( r >= 0 and r < nrows, "row index out of range"    )
    assert( c >= 0 and c < ncols, "column index out of range" )
    let cf = loadValueFrWTF( stream )      # Jordi, WTF is this encoding ?!?!?!!111
    let entry = Coeff( matrix:sel, row:r, col:c, coeff:cf )
    coeffs.add( entry )
  
  user.coeffs = coeffs

#-------------------------------------------------------------------------------

proc parseSection3_PointsIC( stream: Stream, user: var ZKey, sectionLen: int ) =
  let npoints = user.header.npubs + 1
  assert( sectionLen == 64*npoints , "unexpected section length" )
  user.vPoints.pointsIC = loadPointsG1( npoints, stream )

proc parseSection5_PointsA1( stream: Stream, user: var ZKey, sectionLen: int ) =
  let npoints = user.header.nvars
  assert( sectionLen == 64*npoints , "unexpected section length" )
  user.pPoints.pointsA1 = loadPointsG1( npoints, stream )

proc parseSection6_PointsB1( stream: Stream, user: var ZKey, sectionLen: int ) =
  let npoints = user.header.nvars
  assert( sectionLen == 64*npoints , "unexpected section length" )
  user.pPoints.pointsB1 = loadPointsG1( npoints, stream )

proc parseSection7_PointsB2( stream: Stream, user: var ZKey, sectionLen: int ) =
  let npoints = user.header.nvars
  assert( sectionLen == 128*npoints , "unexpected section length" )
  user.pPoints.pointsB2 = loadPointsG2( npoints, stream )

proc parseSection8_PointsC1( stream: Stream, user: var ZKey, sectionLen: int ) =
  let npoints = user.header.nvars - user.header.npubs - 1
  assert( sectionLen == 64*npoints , "unexpected section length" )
  user.pPoints.pointsC1 = loadPointsG1( npoints, stream )

proc parseSection9_PointsH1( stream: Stream, user: var ZKey, sectionLen: int ) =
  let npoints = user.header.domainSize
  assert( sectionLen == 64*npoints , "unexpected section length" )
  user.pPoints.pointsH1 = loadPointsG1( npoints, stream )

#-------------------------------------------------------------------------------

proc zkeyCallback(stream: Stream, sectId: int, sectLen: int, user: var ZKey) = 
  case sectId
    of 1: parseSection1_proverType(  stream, user, sectLen )
    of 2: parseSection2_GrothHeader( stream, user, sectLen )
    of 3: parseSection3_PointsIC(    stream, user, sectLen )
    of 4: parseSection4_Coeffs(      stream, user, sectLen )
    of 5: parseSection5_PointsA1(    stream, user, sectLen )
    of 6: parseSection6_PointsB1(    stream, user, sectLen )
    of 7: parseSection7_PointsB2(    stream, user, sectLen )
    of 8: parseSection8_PointsC1(    stream, user, sectLen )
    of 9: parseSection9_PointsH1(    stream, user, sectLen )
    else: discard

proc parseZKey* (fname: string): ZKey = 
  var zkey : ZKey
  parseContainer( "zkey", 1, fname, zkey, zkeyCallback, proc (id: int): bool = id == 1 )
  parseContainer( "zkey", 1, fname, zkey, zkeyCallback, proc (id: int): bool = id == 2 )
  parseContainer( "zkey", 1, fname, zkey, zkeyCallback, proc (id: int): bool = id >= 3 )
  return zkey

#-------------------------------------------------------------------------------
