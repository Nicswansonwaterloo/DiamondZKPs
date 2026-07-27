# Helpers
from sage.all import (
    Integer,
)
from sage.schemes.elliptic_curves.ell_generic import EllipticCurve_generic
from sage.schemes.elliptic_curves.ell_point import EllipticCurvePoint
from sage.modules.vector_modn_dense import Vector_modn_dense
from sage.modules.free_module_element import FreeModuleElement_generic_dense
from sage.matrix.matrix_generic_dense import Matrix_generic_dense
from sage.matrix.matrix_modn_dense_double import Matrix_modn_dense_double
from vendors.Kummer_Isogeny.kummer_line import KummerLine, KummerPoint
from vendors.Theta_SageMath.theta_structures.couple_point import CouplePoint
from vendors.Theta_SageMath.theta_structures.dimension_two import ThetaPoint, ThetaStructure
import hashlib


def nice_ec_string(E: EllipticCurve_generic):
    a1, a2, a3, a4, a6 = E.a_invariants()
    a1_term = "" if a1 == 0 else (" + xy" if a1 == 1 else f" + {a1}*xy")
    a2_term = "" if a2 == 0 else (" + x^2" if a2 == 1 else f" + {a2}*x^2")
    a3_term = "" if a3 == 0 else (" + y" if a3 == 1 else f" + {a3}*y")
    a4_term = "" if a4 == 0 else (" + x" if a4 == 1 else f" + {a4}*x")
    a6_term = "" if a6 == 0 else f" + {a6}"
    return f"y^2{a1_term}{a3_term} = x^3{a2_term}{a4_term}{a6_term}"


def nice_null_string(null_pt: ThetaStructure):
    return str(null_pt.hyperelliptic_from_theta())


def normalize_and_hash(*args):
    """
    Normalizes various Sage objects into strings in a consistent way, concatenates them,
    and returns SHA256 hash digest of the result.
    """

    def stringify(arg):
        if isinstance(arg, EllipticCurve_generic):
            return f"EllipticCurve j-invariant: {arg.j_invariant()}"
        elif isinstance(arg, int) or isinstance(arg, Integer):
            return f"integer: {arg}"
        elif isinstance(arg, EllipticCurvePoint):
            P = arg
            return f"Point {P} on {P.curve().a_invariants()}"
        elif isinstance(arg, Vector_modn_dense) or isinstance(arg, FreeModuleElement_generic_dense):
            return f"vector: {arg}"
        elif isinstance(arg, Matrix_generic_dense) or isinstance(arg, Matrix_modn_dense_double):
            return f"matrix: {arg}"
        elif isinstance(arg, ThetaStructure):
            return f"theta_struct: {arg}"
        elif isinstance(arg, CouplePoint):
            P1, P2 = arg.P1, arg.P2
            E1, E2 = arg.curves()
            return f"couple_point: ({P1}, {P2}) on ({E1.a_invariants()}, {E2.a_invariants()})"
        elif isinstance(arg, ThetaPoint):
            return f"theta point: {arg}   on struct: {arg.parent()}"
        elif isinstance(arg, KummerPoint):
            return f"kummer point: {arg}  on kummer line: {arg.parent()}"
        elif isinstance(arg, KummerLine):
            return f"kummer line: {arg}"
        else:
            raise ValueError(
                f"Unsupported type for hashing: {type(arg)}\nArgument value:\n{arg}\nArgParent: {arg.parent()}"
            )

    strings_to_hash = []
    for arg in args:
        if isinstance(arg, list) or isinstance(arg, tuple):
            for item in arg:
                strings_to_hash.append(stringify(item))
        else:
            strings_to_hash.append(stringify(arg))

    concatenated_string = "|".join(strings_to_hash)
    hash_output = hashlib.sha256(concatenated_string.encode()).hexdigest()
    return hash_output


