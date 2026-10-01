from copy import copy
from itertools import product

from sage.all import GF, ZZ, Zmod, is_prime_power, matrix, randint

from helpers.product_theta import ProductTheta
from helpers.theta_arithmetic import ThetaArithmetic, UnsupportedProductError, normalize
from helpers.three_isogeny import ThreeIsogenyChain
from vendors.Theta_SageMath.theta_isogenies.product_isogeny import EllipticProductIsogeny
from vendors.Kummer_Isogeny.kummer_isogeny import KummerLineIsogeny
from vendors.Kummer_Isogeny.kummer_line import KummerLine
from vendors.Theta_SageMath.theta_structures.couple_point import CouplePoint
from vendors.Theta_SageMath.theta_structures.dimension_two import ThetaStructure


def is_basis_product(basis, M, E1, E2):
    "Checks if four couple points form a basis for E1xE2[M] with M = 3**e for some e."
    if len(basis) != 4 or M % 3 != 0 or not is_prime_power(M):
        return False

    if any(pt[0] not in E1 or pt[1] not in E2 for pt in basis):
        return False

    if any((M * pt) != CouplePoint(E1(0), E2(0)) for pt in basis):
        return False

    # The weil pairing is symmetric, so we can do a trick to same some computation on the check for non-zeroness of the determinant.
    proj_basis = [(M // 3) * pt for pt in basis]
    e01 = proj_basis[0].weil_pairing(proj_basis[1], 3)
    e02 = proj_basis[0].weil_pairing(proj_basis[2], 3)
    e03 = proj_basis[0].weil_pairing(proj_basis[3], 3)
    e12 = proj_basis[1].weil_pairing(proj_basis[2], 3)
    e13 = proj_basis[1].weil_pairing(proj_basis[3], 3)
    e23 = proj_basis[2].weil_pairing(proj_basis[3], 3)

    # Find the primitive root of unity used for the logs (any non-trivial pairing value works)
    val = e01 if e01 != 1 else (e02 if e02 != 1 else e03)
    if val == 1:
        return False

    def brute_force_dlog(e, val):
        if e == 1:
            return 0
        if e == val:
            return 1
        else:
            return 2

    l01 = brute_force_dlog(e01, val)
    l02 = brute_force_dlog(e02, val)
    l03 = brute_force_dlog(e03, val)
    l12 = brute_force_dlog(e12, val)
    l13 = brute_force_dlog(e13, val)
    l23 = brute_force_dlog(e23, val)

    sqrt_of_det = l01 * l23 - l02 * l13 + l03 * l12
    return sqrt_of_det % 3 != 0


def is_basis_theta(basis, M, theta_struct):
    """Check exact odd order and independence of the projected 3-torsion."""
    if len(basis) != 4 or M % 3 != 0 or not is_prime_power(M):
        return False

    if any(P.parent() != theta_struct for P in basis):
        return False

    A = ThetaArithmetic(theta_struct.coords())
    if A.is_product:
        raise UnsupportedProductError(
            "Product basis verification needs elliptic component signs"
        )

    exponent = 0
    remaining = int(M)
    while remaining > 1:
        remaining //= 3
        exponent += 1

    points = [normalize(A.triple_iter(P.coords(), exponent - 1)) for P in basis]
    if any(P == A.O or normalize(A.triple(P)) != A.O for P in points):
        return False

    P, Q, R, S = points
    if Q == P:
        return False

    PplusQ, PminusQ = A.sums(P, Q)
    span = {P, Q, PplusQ, PminusQ}
    if len(span) != 4 or R in span:
        return False

    # Modulo sign, spans of two and three independent 3-torsion points
    # contain 4 and 13 nonzero points respectively.
    for T in tuple(span):
        span.update(A.sums(T, R))
    span.add(R)

    return len(span) == 13 and S not in span


def check_prod_isomorphic(E1, E2, F1, F2):
    j_in = {E1.j_invariant(), E2.j_invariant()}
    j_targets = {F1.j_invariant(), F2.j_invariant()}
    return j_in == j_targets


def vec_basis_to_pt(vec, basis):
    pt = basis[0] * vec[0]
    for i in range(1, len(basis)):
        pt += basis[i] * vec[i]
    return pt


def is_full_rank(ker_matrix, M):
    # Simply change the base ring to GF(3) and check the rank there
    return ker_matrix.change_ring(GF(3)).rank() == 2


def is_diagonal_and_has_codomain(ker_matrix, basis, M, domain_curves, codomain_curves):
    "Assumes M = 3**e for some e."
    K1 = vec_basis_to_pt(ker_matrix.row(0), basis)
    K2 = vec_basis_to_pt(ker_matrix.row(1), basis)
    zeta1 = K1[0].weil_pairing(K2[0], M)
    zeta2 = K1[1].weil_pairing(K2[1], M)
    if zeta1 != 1 or zeta2 != 1:
        return False  # non-diagonal.

    E1, E2 = domain_curves

    # K1[0] is colinear with K2[0] and they live inside a cyclic subgroup of order M, but we need to figure out which one of these has full rank.
    K_rho1, K_rho2 = None, None
    if (M // 3) * K1[0] != E1(0):
        K_rho1 = K1[0]
    elif (M // 3) * K2[0] != E1(0):
        K_rho1 = K2[0]
    else:
        return False  # no generator of the kernel, so not full rank.

    if (M // 3) * K1[1] != E2(0):
        K_rho2 = K1[1]
    elif (M // 3) * K2[1] != E2(0):
        K_rho2 = K2[1]
    else:
        return False

    # compute codomain with x-only Montgomery isogenies (only the j-invariants are needed)
    F1, F2 = codomain_curves
    E1_kum = KummerLine(E1)
    E2_kum = KummerLine(E2)
    rho1 = KummerLineIsogeny(E1_kum, E1_kum(K_rho1), ZZ(M))
    rho2 = KummerLineIsogeny(E2_kum, E2_kum(K_rho2), ZZ(M))
    G1 = rho1.codomain().curve()
    G2 = rho2.codomain().curve()

    return check_prod_isomorphic(G1, G2, F1, F2)


def rref_zmod(mat):
    """
    Computes the (pseudo) (RREF) of a matrix over Z/MZ.
    Assumes M = 3**e for some e, and that the matrix is full rank.
    - mat is 2x4 matrix over Z/MZ (sage object)
    Returns: a matrix of the form:
    [1, 0, *, *]
    [0, 1, *, *]
    along with basis_permutation, an array of indices which tracks which basis elements are used for the pivots (in case of column swaps).
    """
    # Create a mutable copy to avoid altering the original matrix
    mat = copy(mat)
    perm = [0, 1, 2, 3]
    pivot1 = next(j for j in range(4) if mat[0, j].is_unit())

    if pivot1 != 0:
        mat.swap_columns(0, pivot1)
        perm[0], perm[pivot1] = perm[pivot1], perm[0]

    mat.rescale_row(0, 1 / mat[0, 0])
    mat.add_multiple_of_row(1, 0, -mat[1, 0])

    pivot2 = next(j for j in range(1, 4) if mat[1, j].is_unit())
    if pivot2 != 1:
        mat.swap_columns(1, pivot2)
        perm[1], perm[pivot2] = perm[pivot2], perm[1]

    mat.rescale_row(1, 1 / mat[1, 1])

    # Eliminate the entry directly above the pivot in row 0
    mat.add_multiple_of_row(0, 1, -mat[0, 1])
    return mat, perm


def reorder_basis_and_sums(basis, basis_sums, perm):
    """
    basis: list of 4 elements
    basis_sums: list of 6 elements (ordered B0+B1, B0+B2, B0+B3, B1+B2, B1+B3, B2+B3)
    perm: list of 4 indices representing the new basis order
    """
    pair_to_idx = {(0, 1): 0, (0, 2): 1, (0, 3): 2, (1, 2): 3, (1, 3): 4, (2, 3): 5}
    new_basis = [basis[i] for i in perm]
    new_basis_sums = [
        basis_sums[pair_to_idx[(min(perm[i], perm[j]), max(perm[i], perm[j]))]]
        for i, j in pair_to_idx.keys()
    ]

    return new_basis, new_basis_sums


def theta_matrix_basis_to_pts(ker_matrix, basis, basis_sums, tc_0, M):
    """Recover the two kernel generators, respecting the supplied pairwise sums.

    Reduce to two pivots so each row needs one three-way addition. All scalar
    ladders use tuples; the six sums preserve signs after a basis permutation.
    """
    reduced_matrix, basis_perm = rref_zmod(ker_matrix)
    basis, basis_sums = reorder_basis_and_sums(basis, basis_sums, basis_perm)

    A = ThetaArithmetic(tc_0)
    results = []

    # Each row represents B_row + a*B2 + b*B3. The supplied pairwise
    # sums fix the relative signs for the three-way addition.
    for row, (sum2_idx, sum3_idx) in ((0, (1, 2)), (1, (3, 4))):
        a = int(reduced_matrix[row, 2])
        b = int(reduced_matrix[row, 3])
        X = basis[row]
        Y = A.mul(a, basis[2])
        Z = A.mul(b, basis[3])

        XY = A.mul_add(a, basis[2], X, basis_sums[sum2_idx])
        ZX = A.mul_add(b, basis[3], X, basis_sums[sum3_idx])
        B2plusZ = A.mul_add(b, basis[3], basis[2], basis_sums[5])
        YZ = A.mul_add(a, basis[2], Z, B2plusZ)

        results.append(normalize(A.extended_add(X, Y, Z, XY, YZ, ZX)))

    return tuple(results)


def has_codomain_two_dim(ker_matrix, basis, basis_sums, M, domain: ThetaStructure, codomain_curves):
    "Assumes M = 3**e for some e. ker_matrix is 2x4 matrix of coefficients in the basis. codomain curves are E1, E2 in the product structure that we want to have as codomain."
    if not is_full_rank(ker_matrix, M):
        return False

    O = domain.coords()
    basis = [pt.coords() for pt in basis]
    basis_sums = [pt.coords() for pt in basis_sums]

    K1, K2 = theta_matrix_basis_to_pts(ker_matrix, basis, basis_sums, O, M)

    try:
        # Basis validation and the full-rank matrix already imply exact M-order.
        chain = ThreeIsogenyChain.from_degree(O, (K1, K2), M, perform_checks=False)
        target = chain.codomain.O
    except UnsupportedProductError:
        raise
    except ValueError:
        return False

    if not ThetaArithmetic(target).is_product:
        return False

    F1, F2 = ProductTheta(target).curves
    E1, E2 = codomain_curves
    return check_prod_isomorphic(E1, E2, F1, F2)


def has_codomain_and_mapping_two_dim_and_nondiagonal(
    above_ker_points, domain_curves, codomain, N, points, point_images
):
    T1, T2 = above_ker_points
    K1, K2 = 4 * T1, 4 * T2

    if (
        above_ker_points[0].curves() != domain_curves
        or above_ker_points[1].curves() != domain_curves
    ):
        return False

    E1, E2 = domain_curves

    if (N * K1) != CouplePoint(E1(0), E2(0)) or (N * K2) != CouplePoint(E1(0), E2(0)):
        return False  # Not N-torsion

    zeta1 = K1[0].weil_pairing(K2[0], N)
    zeta2 = K1[1].weil_pairing(K2[1], N)
    if zeta1 == 1 or zeta2 == 1:
        return False  # kernel is diagonal
    if zeta1 * zeta2 != 1:
        return False  # kernel not isotropic.
    if zeta1 ** (N // 2) == 1:
        return False  # kernel not maximal.

    chain = EllipticProductIsogeny.from_degree(above_ker_points, N, split=False)
    computed_A = chain.codomain()
    computed_images = [chain(P) for P in points]
    if computed_A != codomain:
        return False

    if point_images != computed_images:
        return False

    return True


def randomize_basis_two_dim(basis, M, kernel_matrix=None):
    change_of_basis = matrix(Zmod(M), 4, 4, [randint(0, M - 1) for _ in range(16)])
    while not change_of_basis.det().is_unit():
        change_of_basis = matrix(Zmod(M), 4, 4, [randint(0, M - 1) for _ in range(16)])

    random_basis = [
        change_of_basis[0, 0] * basis[0]
        + change_of_basis[0, 1] * basis[1]
        + change_of_basis[0, 2] * basis[2]
        + change_of_basis[0, 3] * basis[3],
        change_of_basis[1, 0] * basis[0]
        + change_of_basis[1, 1] * basis[1]
        + change_of_basis[1, 2] * basis[2]
        + change_of_basis[1, 3] * basis[3],
        change_of_basis[2, 0] * basis[0]
        + change_of_basis[2, 1] * basis[1]
        + change_of_basis[2, 2] * basis[2]
        + change_of_basis[2, 3] * basis[3],
        change_of_basis[3, 0] * basis[0]
        + change_of_basis[3, 1] * basis[1]
        + change_of_basis[3, 2] * basis[2]
        + change_of_basis[3, 3] * basis[3],
    ]

    if kernel_matrix is not None:
        sk_in_random_basis = kernel_matrix * change_of_basis.inverse()
        return random_basis, change_of_basis, sk_in_random_basis
    else:
        return random_basis, change_of_basis


def randomize_diagonal_kernel(K1, K2, M):
    change_of_basis = matrix(Zmod(M), 2, 2, [randint(0, M - 1) for _ in range(4)])
    while not change_of_basis.det().is_unit():
        change_of_basis = matrix(Zmod(M), 2, 2, [randint(0, M - 1) for _ in range(4)])

    X1 = CouplePoint(change_of_basis[0, 0] * K1, change_of_basis[0, 1] * K2)
    X2 = CouplePoint(change_of_basis[1, 0] * K1, change_of_basis[1, 1] * K2)
    return X1, X2, change_of_basis


def get_points_above_kernel(K1, K2, N):
    """Find compatible T1, T2 such that 4*T1 = K1 and 4*T2 = K2."""
    T1_0_cands = K1[0].division_points(4)
    T1_1_cands = K1[1].division_points(4)
    T2_0_cands = K2[0].division_points(4)
    T2_1_cands = K2[1].division_points(4)

    zeta = K1[0].weil_pairing(K2[0], 4 * N)

    for (t1_0, t1_1), (t2_0, t2_1) in product(
        product(T1_0_cands, T1_1_cands),
        product(T2_0_cands, T2_1_cands),
    ):
        if (
            t1_0.weil_pairing(t2_0, 4 * N) ** 16 == zeta
            and t1_1.weil_pairing(t2_1, 4 * N) ** 16 == 1 / zeta
        ):
            return CouplePoint(t1_0, t1_1), CouplePoint(t2_0, t2_1)

    raise ValueError("No points above the Kani kernel found")
