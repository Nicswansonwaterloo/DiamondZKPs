"""Full-degree RanIso port from SQIsign2DSquare.

Original Julia source:
https://github.com/Kaizhan-Lin/SQIsign2DSquare
commit 176634178cf8b42e7261eb383911ea5781a377d2

The layout and names follow ``src/rii/quat_action.jl``,
``src/rii/d2isogeny.jl``, and ``src/rii/rii.jl``.  Sage elliptic curve
points replace the original x-only Montgomery arithmetic.
"""

from dataclasses import dataclass

from sage.all import (
    GF,
    EllipticCurve,
    Integer,
    Zmod,
    discrete_log,
    identity_matrix,
    inverse_mod,
    matrix,
)

from vendors.SQIsign2DSquare.quaternion import FullRepresentInteger
from vendors.Theta_SageMath.theta_isogenies.gluing_isogeny import GluingThetaIsogeny
from vendors.Theta_SageMath.theta_isogenies.isogeny import ThetaIsogeny
from vendors.Theta_SageMath.theta_isogenies.isogeny_sqrt import (
    ThetaIsogeny2,
    ThetaIsogeny4,
)
from vendors.Theta_SageMath.theta_isogenies.isomorphism import SplittingIsomorphism
from vendors.Theta_SageMath.theta_structures.couple_point import CouplePoint
from vendors.Theta_SageMath.theta_structures.split_structure import SplitThetaStructure
from vendors.Theta_SageMath.utilities.strategy import optimised_strategy
from vendors.Theta_SageMath.utilities.supersingular import torsion_basis


def _get_coefficients_wrt(P, Q, R, order):
    w_PQ = P.weil_pairing(Q, order)
    a = discrete_log(R.weil_pairing(Q, order), w_PQ, ord=order)
    b = discrete_log(R.weil_pairing(P, order), 1 / w_PQ, ord=order)
    assert R == a * P + b * Q
    return Integer(a), Integer(b)


def _map_matrix(P, Q, order, function):
    columns = [_get_coefficients_wrt(P, Q, function(R), order) for R in (P, Q)]
    return matrix(Zmod(order), columns).transpose()


def _i_action(E, sqrt_minus_one, P):
    if not P:
        return P
    return E(-P[0], sqrt_minus_one * P[1])


def _frobenius_action(E, p, P):
    if not P:
        return P
    return E(P[0] ** p, P[1] ** p)


def _order_basis_matrices_odd(E, P, Q, order, p, sqrt_minus_one):
    M_i = _map_matrix(P, Q, order, lambda R: _i_action(E, sqrt_minus_one, R))
    M_j = _map_matrix(P, Q, order, lambda R: _frobenius_action(E, p, R))
    M_ij = inverse_mod(2, order) * (M_i + M_j)
    M_1k = identity_matrix(Zmod(order), 2) + M_i * M_ij
    return (M_i, M_ij, M_1k)


def _order_basis_matrices_even(E, P, Q, order, p, sqrt_minus_one):
    """Compute the maximal-order action using compatible 2N-division points."""

    Fp4 = E.base_ring().extension(2, "u")
    E4 = E.base_extend(Fp4)
    P4 = E4(P)
    Q4 = E4(Q)
    twice_order = 2 * order

    P_above = P4.division_points(2)
    Q_above = Q4.division_points(2)
    R = S = None
    # Pairings here lie in 2-power roots of unity. For z in mu_{2^e},
    # ord(z) = 2^e iff z^(2^(e-1)) != 1.
    half_twice_order = twice_order // 2
    for R_cand in P_above:
        for S_cand in Q_above:
            zeta = R_cand.weil_pairing(S_cand, twice_order)
            if zeta**half_twice_order != 1:
                R, S = R_cand, S_cand
                break
        if R is not None:
            break
    if R is None:
        raise ValueError("could not find compatible points above the 2-power basis")

    sqrt_minus_one_4 = Fp4(sqrt_minus_one)
    M_i_2N = _map_matrix(
        R,
        S,
        twice_order,
        lambda T: _i_action(E4, sqrt_minus_one_4, T),
    )
    M_j_2N = _map_matrix(
        R,
        S,
        twice_order,
        lambda T: _frobenius_action(E4, p, T),
    )

    half_entries = []
    for value in (M_i_2N + M_j_2N).list():
        value = Integer(value)
        if value % 2:
            raise ValueError("the maximal-order half action is not integral")
        half_entries.append((value // 2) % order)

    ring = Zmod(order)
    M_i = M_i_2N.change_ring(ring)
    M_ij = matrix(ring, 2, 2, half_entries)
    M_1k = identity_matrix(ring, 2) + M_i * M_ij
    return (M_i, M_ij, M_1k)


@dataclass
class E0Data:
    E0: object
    P2e: object
    Q2e: object
    OddTorsionBases: tuple
    Matrices_2e: tuple
    Matrices_odd: tuple


@dataclass
class GlobalData:
    p: Integer
    ExponentFull: int
    ExponentCofactor: int
    Cofactor: Integer
    AuxiliaryCofactor: Integer
    Fp2: object
    Fp2_i: object
    E0_data: E0Data


def make_precomputed_values(p, e2, e3, Fp2=None, auxiliary_cofactor=1):
    """Sage analogue of the Julia parameter files' precomputation routine.

    The proof-of-concept reserves two additional rational 2-torsion levels for
    the repository's existing product-isogeny evaluator.  ``ExponentFull``
    remains the exponent of the full-degree RanIso construction.

    Unlike the original SQIsign2DSquare parameters, the ambient prime may have
    an auxiliary factor:

        p + 1 = 4 * 2^e2 * 3^e3 * auxiliary_cofactor.

    This factor is not part of RanIso's accessible 3-power isogeny.  It only
    appears in the scalar used by ``torsion_basis`` to project random points
    onto the required 2- and 3-power torsion.
    """

    p = Integer(p)
    N = Integer(2) ** e2
    Cofactor = Integer(3) ** e3
    auxiliary_cofactor = Integer(auxiliary_cofactor)
    if auxiliary_cofactor < 1:
        raise ValueError("the auxiliary cofactor must be positive")
    if p != 4 * N * Cofactor * auxiliary_cofactor - 1:
        raise ValueError(
            "this RanIso port requires "
            "p = 4 * 2^e2 * 3^e3 * auxiliary_cofactor - 1"
        )

    if Fp2 is None:
        Fp2 = GF(p**2, modulus=[1, 0, 1], names="i")
    Fp2_i = Fp2.gen()
    E0 = EllipticCurve(Fp2, [1, 0])
    E0.set_order((p + 1) ** 2)

    P2e, Q2e = torsion_basis(E0, N)
    P3e, Q3e = torsion_basis(E0, Cofactor)
    Matrices_2e = _order_basis_matrices_even(E0, P2e, Q2e, N, p, Fp2_i)
    Matrices_odd = (
        _order_basis_matrices_odd(E0, P3e, Q3e, Cofactor, p, Fp2_i),
    )

    E0_data = E0Data(
        E0=E0,
        P2e=P2e,
        Q2e=Q2e,
        OddTorsionBases=((P3e, Q3e),),
        Matrices_2e=Matrices_2e,
        Matrices_odd=Matrices_odd,
    )
    return GlobalData(
        p,
        e2,
        e3,
        Cofactor,
        auxiliary_cofactor,
        Fp2,
        Fp2_i,
        E0_data,
    )


def quaternion_to_matrix(alpha, Ms, order):
    """Port of ``quat_action.jl::quaternion_to_matrix``."""

    ring = Zmod(order)
    return (
        alpha[0] * identity_matrix(ring, 2)
        + alpha[1] * Ms[0]
        + alpha[2] * Ms[1]
        + alpha[3] * Ms[2]
    )


def action_on_torsion_basis(alpha, P, Q, Ms, order):
    """Port of ``quat_action.jl::action_on_torsion_basis``."""

    M = quaternion_to_matrix(alpha, Ms, order)
    P_new = Integer(M[0, 0]) * P + Integer(M[1, 0]) * Q
    Q_new = Integer(M[0, 1]) * P + Integer(M[1, 1]) * Q
    return P_new, Q_new


def kernel_coefficients(alpha, ell, e, Ms):
    """Port of ``quat_action.jl::kernel_coefficients``."""

    order = Integer(ell) ** e
    M = quaternion_to_matrix(alpha, Ms, order)
    if M[0, 0] % ell != 0 or M[0, 1] % ell != 0:
        a, b = M[0, 1], -M[0, 0]
    else:
        a, b = M[1, 1], -M[1, 0]

    if a % ell != 0:
        b = b * inverse_mod(Integer(a), order)
        return Integer(1), Integer(b)

    a = a * inverse_mod(Integer(b), order)
    return Integer(a), Integer(1)


def kernel_generator(P, Q, alpha, ell, e, Ms):
    """Port of ``quat_action.jl::kernel_generator``."""

    a, b = kernel_coefficients(alpha, ell, e, Ms)
    return a * P + b * Q


class ProductIsogenySqrt:
    """Sage theta implementation of the Julia ``product_isogeny_sqrt`` call."""

    def __init__(self, kernel, n):
        self.n = n
        self._domain = kernel[0].curves()
        self._phis = self._isogeny_chain(kernel)
        self._theta_codomain = self._phis[-1].codomain()
        self._splitting_iso = SplittingIsomorphism(self._theta_codomain)
        split_theta = self._splitting_iso.codomain()
        self._splitting = SplitThetaStructure(split_theta)
        self._codomain = self._splitting.curves()

    def _isogeny_chain(self, kernel):
        Tp1, Tp2 = kernel
        isogeny_chain = []
        strategy = optimised_strategy(self.n - 2)
        strat_idx = 0
        level = [0]
        ker = (Tp1, Tp2)
        kernel_elements = [ker]

        for k in range(self.n - 2):
            prev = sum(level)
            ker = kernel_elements[-1]
            while prev != self.n - 3 - k:
                level.append(strategy[strat_idx])
                Tp1 = ker[0].double_iter(strategy[strat_idx])
                Tp2 = ker[1].double_iter(strategy[strat_idx])
                ker = (Tp1, Tp2)
                kernel_elements.append(ker)
                prev += strategy[strat_idx]
                strat_idx += 1

            Tp1, Tp2 = ker
            if k == 0:
                phi = GluingThetaIsogeny(Tp1, Tp2)
            else:
                phi = ThetaIsogeny(Th, Tp1, Tp2)
            Th = phi.codomain()
            isogeny_chain.append(phi)

            if k != self.n - 3:
                kernel_elements.pop()
            level.pop()
            kernel_elements = [
                (phi(T1), phi(T2)) for T1, T2 in kernel_elements
            ]

        Tp1, Tp2 = kernel_elements[0]
        phi = ThetaIsogeny4(Th, Tp1, Tp2, hadamard=(False, False))
        isogeny_chain.append(phi)
        Th = phi.codomain()
        phi = ThetaIsogeny2(Th, hadamard=(True, False))
        isogeny_chain.append(phi)
        return isogeny_chain

    def domain(self):
        return self._domain

    def codomain(self):
        return self._codomain

    def __call__(self, P):
        for phi in self._phis:
            P = phi(P)
        P = self._splitting_iso(P)
        return self._splitting(P)


def d2isogeny(E1, E2, P1, Q1, P2, Q2, exp, d, eval_points=()):
    """Port of the full-degree ``d2isogeny`` call used by ``RanIso``."""

    kernel = (CouplePoint(P1, P2), CouplePoint(Q1, Q2))
    Phi = ProductIsogenySqrt(kernel, exp)
    images = tuple(Phi(P) for P in eval_points)
    return Phi, images


def _same_up_to_sign(P, Q):
    return P == Q or P == -Q


def _factor_permutation(Phi, P, Q, d, order, E2):
    """Match Julia's Weil-pairing selection while retaining both factors."""

    zero = E2(0)
    image_P = Phi(CouplePoint(P, zero))
    image_Q = Phi(CouplePoint(Q, zero))
    image_PQ = Phi(CouplePoint(P + Q, zero))
    components_P = [image_P[0], image_P[1]]
    components_Q = [image_Q[0], image_Q[1]]

    for idx in range(2):
        if not _same_up_to_sign(components_P[idx] + components_Q[idx], image_PQ[idx]):
            components_Q[idx] = -components_Q[idx]

    source_pairing = P.weil_pairing(Q, order)
    pairings = [
        components_P[idx].weil_pairing(components_Q[idx], order)
        for idx in range(2)
    ]
    if pairings[0] == source_pairing**d:
        return (0, 1)
    if pairings[1] == source_pairing**d:
        return (1, 0)
    raise ValueError("could not identify the d-isogeny factor of the RanIso codomain")


@dataclass
class RanIsoResult:
    E0: object
    EA: object
    EB: object
    EAB: object
    kernel: tuple
    Phi_raw: ProductIsogenySqrt
    codomain_permutation: tuple
    odd_images: tuple
    alpha: object
    accessible_kernel: object
    accessible_isogeny: object

    def Phi(self, P):
        image = self.Phi_raw(P)
        return CouplePoint(
            image[self.codomain_permutation[0]],
            image[self.codomain_permutation[1]],
        )


def RanIso(d, global_data, compute_odd_points=False):
    """Port of ``rii.jl::RanIso`` (the full-degree variant)."""

    deg_dim2 = Integer(1) << global_data.ExponentFull
    deg_sec = d * (deg_dim2 - d) * global_data.Cofactor
    E0_data = global_data.E0_data
    E0 = E0_data.E0
    P0, Q0 = E0_data.P2e, E0_data.Q2e

    # generate the endomorphism
    alpha, found = FullRepresentInteger(deg_sec, global_data.p)
    while not found or alpha.content() % 3 == 0:
        alpha, found = FullRepresentInteger(deg_sec, global_data.p)

    P3e, Q3e = E0_data.OddTorsionBases[0]
    d_inv = inverse_mod(d * global_data.Cofactor, deg_dim2)
    scaled_alpha = d_inv * alpha
    P, Q = action_on_torsion_basis(
        scaled_alpha,
        P0,
        Q0,
        E0_data.Matrices_2e,
        deg_dim2,
    )

    # compute the C-isogeny
    ker = kernel_generator(
        P3e,
        Q3e,
        alpha.involution(),
        3,
        global_data.ExponentCofactor,
        E0_data.Matrices_odd[0],
    )
    eta = E0.isogeny(ker, algorithm="factored", model="montgomery")
    EAB = eta.codomain()
    EAB.set_order((global_data.p + 1) ** 2)
    P, Q = eta(P), eta(Q)

    # compute the two-dimensional isogeny
    odd_points = ()
    if compute_odd_points:
        odd_points = (
            CouplePoint(P3e, EAB(0)),
            CouplePoint(Q3e, EAB(0)),
            CouplePoint(P3e - Q3e, EAB(0)),
        )
    Phi, odd_images_raw = d2isogeny(
        E0,
        EAB,
        P0,
        Q0,
        P,
        Q,
        global_data.ExponentFull,
        d,
        odd_points,
    )

    permutation = _factor_permutation(
        Phi,
        P3e,
        Q3e,
        d,
        global_data.Cofactor,
        EAB,
    )
    EA = Phi.codomain()[permutation[0]]
    EB = Phi.codomain()[permutation[1]]
    EA.set_order((global_data.p + 1) ** 2)
    EB.set_order((global_data.p + 1) ** 2)
    odd_images = tuple(
        CouplePoint(image[permutation[0]], image[permutation[1]])
        for image in odd_images_raw
    )

    kernel = (CouplePoint(P0, P), CouplePoint(Q0, Q))
    return RanIsoResult(
        E0=E0,
        EA=EA,
        EB=EB,
        EAB=EAB,
        kernel=kernel,
        Phi_raw=Phi,
        codomain_permutation=permutation,
        odd_images=odd_images,
        alpha=alpha,
        accessible_kernel=ker,
        accessible_isogeny=eta,
    )
