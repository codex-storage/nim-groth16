#
# the `alt-bn128` elliptic curve
#
# See for example <https://hackmd.io/@jpw/bn254>
#
# p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
# r = 21888242871839275222246405745257275088548364400416034343698204186575808495617
#
# equation: y^2 = x^3 + 3
#

#-------------------------------------------------------------------------------

import groth16/bn128/fields
import groth16/bn128/curves
import groth16/bn128/msm
import groth16/bn128/io
import groth16/bn128/rnd
import groth16/bn128/debug

#-------------------

export fields
export curves
export msm
export io
export rnd
export debug

#-------------------------------------------------------------------------------

