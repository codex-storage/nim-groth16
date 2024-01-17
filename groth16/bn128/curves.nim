#
# the `alt-bn128` elliptic curve
#
# See for example <https://hackmd.io/@jpw/bn254>
#
#   p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
#   r = 21888242871839275222246405745257275088548364400416034343698204186575808495617
#
# equation: y^2 = x^3 + 3
#


#import constantine/platforms/abstractions
#import constantine/math/isogenies/frobenius

import constantine/math/arithmetic    except Fp, Fr
import constantine/math/io/io_fields  except Fp, Fr
import constantine/math/io/io_bigints
import constantine/math/config/curves  

import constantine/math/config/type_ff          as tff except Fp, Fr
import constantine/math/extension_fields/towers as ext except Fp, Fp2, Fp12, Fr

import constantine/math/elliptic/ec_shortweierstrass_affine     as aff 
import constantine/math/elliptic/ec_shortweierstrass_projective as prj 
import constantine/math/pairings/pairings_bn                    as ate 
import constantine/math/elliptic/ec_scalar_mul                  as scl 

import groth16/bn128/fields

#-------------------------------------------------------------------------------

type G1*   = aff.ECP_ShortW_Aff[Fp , aff.G1]
type G2*   = aff.ECP_ShortW_Aff[Fp2, aff.G2]

type ProjG1*  = prj.ECP_ShortW_Prj[Fp , prj.G1]
type ProjG2*  = prj.ECP_ShortW_Prj[Fp2, prj.G2]

#-------------------------------------------------------------------------------

func unsafeMkG1* ( X, Y: Fp ) : G1 =
  return aff.ECP_ShortW_Aff[Fp, aff.G1](x: X, y: Y)

func unsafeMkG2* ( X, Y: Fp2 ) : G2 =
  return aff.ECP_ShortW_Aff[Fp2, aff.G2](x: X, y: Y)

#-------------------------------------------------------------------------------

const infG1*   : G1  = unsafeMkG1( zeroFp  , zeroFp  )
const infG2*   : G2  = unsafeMkG2( zeroFp2 , zeroFp2 )

#-------------------------------------------------------------------------------

func checkCurveEqG1*( x, y: Fp ) : bool =
  if bool(isZero(x)) and bool(isZero(y)):
    # the point at infinity is on the curve by definition
    return true
  else:
    var x2 : Fp = squareFp(x)
    var y2 : Fp = squareFp(y)
    var x3 : Fp = x2 * x
    var eq : Fp
    eq =  x3
    eq += intToFp(3)
    eq -= y2
    # echo("eq = ",toDecimalFp(eq))
    return (bool(isZero(eq)))

#---------------------------------------

# y^2 = x^3 + B
# B = b1 + bu*u
# b1 = 19485874751759354771024239261021720505790618469301721065564631296452457478373
# b2 = 266929791119991161246907387137283842545076965332900288569378510910307636690
const twistCoeffB_1 : Fp  = fromHex(Fp, "0x2b149d40ceb8aaae81be18991be06ac3b5b4c5e559dbefa33267e6dc24a138e5")
const twistCoeffB_u : Fp  = fromHex(Fp, "0x009713b03af0fed4cd2cafadeed8fdf4a74fa084e52d1852e4a2bd0685c315d2")
const twistCoeffB   : Fp2 = mkFp2( twistCoeffB_1 , twistCoeffB_u )

func checkCurveEqG2*( x, y: Fp2 ) : bool =
  if isZeroFp2(x) and isZeroFp2(y):
    # the point at infinity is on the curve by definition
    return true
  else:
    var x2 : Fp2 = squareFp2(x)
    var y2 : Fp2 = squareFp2(y)
    var x3 : Fp2 = x2 * x;
    var eq : Fp2
    eq =  x3
    eq += twistCoeffB
    eq -= y2
    return isZeroFp2(eq)

#-------------------------------------------------------------------------------

func mkG1*( x, y: Fp ) : G1 =
  if isZeroFp(x) and isZeroFp(y):
    return infG1
  else:
    assert( checkCurveEqG1(x,y) , "mkG1: not a G1 curve point" )
    return unsafeMkG1(x,y)

func mkG2*( x, y: Fp2 ) : G2 =
  if isZeroFp2(x) and isZeroFp2(y):
    return infG2
  else:
    assert( checkCurveEqG2(x,y) , "mkG2: not a G2 curve point" )
    return unsafeMkG2(x,y)

#-------------------------------------------------------------------------------
# group generators

const gen1_x  : Fp = fromHex(Fp, "0x01")
const gen1_y  : Fp = fromHex(Fp, "0x02")

const gen2_xi : Fp = fromHex(Fp, "0x1adcd0ed10df9cb87040f46655e3808f98aa68a570acf5b0bde23fab1f149701")
const gen2_xu : Fp = fromHex(Fp, "0x09e847e9f05a6082c3cd2a1d0a3a82e6fbfbe620f7f31269fa15d21c1c13b23b")
const gen2_yi : Fp = fromHex(Fp, "0x056c01168a5319461f7ca7aa19d4fcfd1c7cdf52dbfc4cbee6f915250b7f6fc8")
const gen2_yu : Fp = fromHex(Fp, "0x0efe500a2d02dd77f5f401329f30895df553b878fc3c0dadaaa86456a623235c")

const gen2_x  : Fp2 = mkFp2( gen2_xi, gen2_xu )
const gen2_y  : Fp2 = mkFp2( gen2_yi, gen2_yu )

const gen1* : G1 = unsafeMkG1( gen1_x, gen1_y )
const gen2* : G2 = unsafeMkG2( gen2_x, gen2_y )

#-------------------------------------------------------------------------------

func isOnCurveG1* ( p: G1 ) : bool =
  return checkCurveEqG1( p.x, p.y )

func isOnCurveG2* ( p: G2 ) : bool =
  return checkCurveEqG2( p.x, p.y )

#===============================================================================

func addG1*(p,q: G1): G1 =
  var r, x, y : ProjG1
  prj.fromAffine(x, p)
  prj.fromAffine(y, q)
  prj.sum(r, x, y)
  var s : G1
  prj.affine(s, r)
  return s

#---------------------------------------

func addG2*(p,q: G2): G2 =
  var r, x, y : ProjG2
  prj.fromAffine(x, p)
  prj.fromAffine(y, q)
  prj.sum(r, x, y)
  var s : G2
  prj.affine(s, r)
  return s

func negG1*(p: G1): G1 =
  var r : G1 = p
  neg(r)
  return r

func negG2*(p: G2): G2 =
  var r : G2 = p
  neg(r)
  return r

#---------------------------------------

func `+`*(p,q: G1): G1 = addG1(p,q)
func `+`*(p,q: G2): G2 = addG2(p,q)

func `+=`*(p: var G1, q: G1) =    p = addG1(p,q)
func `+=`*(p: var G2, q: G2) =    p = addG2(p,q)

func `-=`*(p: var G1, q: G1) =    p = addG1(p,negG1(q))
func `-=`*(p: var G2, q: G2) =    p = addG2(p,negG2(q))

#-------------------------------------------------------------------------------
#
# (affine) scalar multiplication
#

func `**`*( coeff: Fr , point: G1 ) : G1 =
  var q : ProjG1
  prj.fromAffine( q , point )
  scl.scalarMulGeneric(  q , coeff.toBig() )
  var r : G1
  prj.affine( r, q )
  return r

func `**`*( coeff: Fr , point: G2 ) : G2 =
  var q : ProjG2
  prj.fromAffine( q , point )
  scl.scalarMulGeneric(  q , coeff.toBig() )
  var r : G2
  prj.affine( r, q )
  return r

#-------------------

func `**`*( coeff: BigInt , point: G1 ) : G1 =
  var q : ProjG1
  prj.fromAffine( q , point )
  scl.scalarMulGeneric(  q , coeff )
  var r : G1
  prj.affine( r, q )
  return r

func `**`*( coeff: BigInt , point: G2 ) : G2 =
  var q : ProjG2
  prj.fromAffine( q , point )
  scl.scalarMulGeneric(  q , coeff )
  var r : G2
  prj.affine( r, q )
  return r

#-------------------------------------------------------------------------------

func pairing* (p: G1, q: G2) : Fp12 =
  var t : Fp12
  ate.pairing_bn[BN254Snarks]( t, p, q )
  return t

#-------------------------------------------------------------------------------

proc sanityCheckGroupGen*() =
  echo( "gen1 on the curve  = ", checkCurveEqG1(gen1.x,gen1.y) )
  echo( "gen2 on the curve  = ", checkCurveEqG2(gen2.x,gen2.y) )
  echo( "order of gen1 is R = ", (not bool(isInf(gen1))) and bool(isInf(primeR ** gen1)) )
  echo( "order of gen2 is R = ", (not bool(isInf(gen2))) and bool(isInf(primeR ** gen2)) )

#-------------------------------------------------------------------------------
