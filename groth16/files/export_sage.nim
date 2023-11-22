
#
# export proof, public input and verifier as a SageMath script
#

import std/strutils
import std/streams

import constantine/math/arithmetic   except Fp, Fr

import groth16/bn128
import groth16/zkey_types
from groth16/prover import Proof

#-------------------------------------------------------------------------------

func toSpaces(str: string): string = spaces(str.len)

func sageFp(prefix: string, x: Fp): string = prefix & "Fp(" & toDecimalFp(x) & ")"
func sageFr(prefix: string, x: Fr): string = prefix & "Fr(" & toDecimalFr(x) & ")"

func sageFp2(prefix: string, z: Fp2): string = 
  sageFp( prefix           & "mkFp2(" , z.coords[0]) & ",\n" & 
  sageFp( toSpaces(prefix) & "      " , z.coords[1]) & ")"

func sageG1(prefix: string, p: G1): string = 
  sageFp( prefix           & "E(" , p.x) & ",\n" & 
  sageFp( toSpaces(prefix) & "  " , p.y) & ")"

func sageG2(prefix: string, p: G2): string =
  sageFp2( prefix           & "E2(" , p.x) & ",\n" & 
  sageFp2( toSpaces(prefix) & "   " , p.y) & ")"

#-------------------------------------------------------------------------------

proc exportVKey(h: Stream, vkey: VKey ) = 
  let spec = vkey.spec
  h.writeLine("alpha1 = \\") ; h.writeLine(sageG1("  ", spec.alpha1))
  h.writeLine("beta2  = \\") ; h.writeLine(sageG2("  ", spec.beta2 ))
  h.writeLine("gamma2 = \\") ; h.writeLine(sageG2("  ", spec.gamma2))
  h.writeLine("delta2 = \\") ; h.writeLine(sageG2("  ", spec.delta2))

  let pts = vkey.vpoints.pointsIC 
  h.writeLine("pointsIC = \\")
  for i in 0..<pts.len:
    let prefix  = if (i==0):        "  [ " else: "    "
    let postfix = if (i<pts.len-1): ","    else: " ]" 
    h.writeLine( sageG1(prefix, pts[i]) & postfix )

#---------------------------------------

proc exportProof*(h: Stream, prf: Proof ) = 
  h.writeLine("piA = \\") ; h.writeLine(sageG1("  ", prf.pi_a ))
  h.writeLine("piB = \\") ; h.writeLine(sageG2("  ", prf.pi_b ))
  h.writeLine("piC = \\") ; h.writeLine(sageG1("  ", prf.pi_c ))
 
  # note: the first element is just the constant 1
  let coeffs = prf.publicIO
  h.writeLine("pubIO = \\")
  for i in 0..<coeffs.len:
    let prefix  = if (i==0):           "  [ " else: "    "
    let postfix = if (i<coeffs.len-1): ","    else: " ]" 
    h.writeLine( prefix & toDecimalFr(coeffs[i]) & postfix )

#-------------------------------------------------------------------------------

const sage_bn128_lines : seq[string] = 
  @[ "# BN128 elliptic curve"
  , "p  = 21888242871839275222246405745257275088696311157297823662689037894645226208583"
  , "r  = 21888242871839275222246405745257275088548364400416034343698204186575808495617"
  , "h  = 1"
  , "Fp = GF(p)"
  , "Fr = GF(r)"
  , "A  = Fp(0)"
  , "B  = Fp(3)"
  , "E  = EllipticCurve(Fp,[A,B])"
  , "gx = Fp(1)"
  , "gy = Fp(2)"
  , "gen = E(gx,gy)  # subgroup generator"
  , "print(\"scalar field check: \", gen.additive_order() == r )"
  , "print(\"cofactor check:     \", E.cardinality() == r*h )"
  , ""
  , "# r and trace of Frobenius from the BN parameter x"
  , "x = 4965661367192848881"
  , "bn_r=36*x^4+36*x^3+18*x^2+6*x+1"
  , "bn_t=6*x^2+1"
  , "print(\"BN r = \",bn_r)"
  , "print(\"BN t = \",bn_t)"
  , "print(\"test p+1 === t (mod r) : \", mod(p+1-bn_t,r) )"
  , ""
  , "# extension tower"
  , "R.<x>   = Fp[]"
  , "Fp2.<u> = Fp.extension(x^2+1)"
  , "def mkFp2(a,b):"
  , "  return ( a + u*b )"
  , "R.<x>    = Fp2[]"
  , "Fp12.<w> = Fp2.extension(x^6 - (9+u))"
  , "E12 = E.base_extend(Fp12)"
  , ""
  , "# twisted curve"
  , "B_twist = Fp2(19485874751759354771024239261021720505790618469301721065564631296452457478373 + 266929791119991161246907387137283842545076965332900288569378510910307636690*u )"
  , "E2 = EllipticCurve(Fp2,[0,B_twist])"
  , "size_E2     = E2.cardinality();"
  , "cofactor_E2 = size_E2 / r;"
  , "print(\"|E2|  = \", size_E2 );"
  , "print(\"h(E2) = \", cofactor_E2 );"
  , ""
  , "# map from E2 to E12"
  , "def Psi(pt):"
  , "  pt.normalize_coordinates()"
  , "  x = pt[0]"
  , "  y = pt[1]"
  , "  return E12( Fp12(w^2 * x) , Fp12(w^3 * y) )"
  , ""
  , "def pairing(P,Q):"
  , "  return E12(P).ate_pairing( Psi(Q), n=r, k=12, t=bn_t, q=p^12 )"
  , ""
  ]

const sage_bn128 : string = join(sage_bn128_lines, sep="\n")

#-------------------------------------------------------------------------------

const verify_lines : seq[string] = 
  @[ "pubG1 = pointsIC[0]"
  , "for i in [1..len(pubIO)-1]:"
  , "  pubG1 = pubG1 + pubIO[i]*pointsIC[i]"
  , ""
  , "lhs  = pairing( -piA   , piB    )"
  , "rhs1 = pairing( alpha1 , beta2  )"
  , "rhs2 = pairing( piC    , delta2 )"
  , "rhs3 = pairing( pubG1  , gamma2 )"
  , "eq = lhs * rhs1 * rhs2 * rhs3"
  , "print(\"verification suceeded =\\n\",eq == 1)"
  ]

const verify_script : string = join(verify_lines, sep="\n")

#-------------------------------------------------------------------------------

proc exportSage*(fpath: string, vkey: VKey, prf: Proof) = 

  let h = openFileStream(fpath, fmWrite)
  defer: h.close()

  h.writeLine(sage_bn128)
  h.exportVKey(vkey);
  h.exportProof(prf);
  h.writeLine(verify_script)

#-------------------------------------------------------------------------------

