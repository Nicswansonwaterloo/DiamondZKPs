from itertools import product

from sage.all import GF, Zmod, is_prime_power, matrix, randint

from helpers.two_dim_wrappers import get_codomain_from_tc_odd, mapping_E0xE1_to_A_even
from vendors.EllEll_Isogeny_Sage.class_theta import Coord, NullCoord
from vendors.EllEll_Isogeny_Sage.func_elliptic import (
    Is_Elliptic_product,
    Legendre_to_Elliptic,
    Lv2tnp_to_Legendre,
    Theta_Hadamard,
)
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
    if len(basis) != 4 or M % 3 != 0 or not is_prime_power(M):
        return False

    if any(pt.parent() != theta_struct for pt in basis):
        return False

    proj_basis = [(M // 3) * pt for pt in basis]

    if any(not (3 * pt).is_zero() for pt in proj_basis):
        return False

    # First switch model for tc_point
    K = theta_struct.base_ring()
    tc_0 = NullCoord(theta_struct.null_point().coords(), 1, K)
    Q1, Q2, Q3, Q4 = [Coord(pt.coords(), 1, K) for pt in proj_basis]

    # Here, we must now check that the 3-torsion forms a basis for theta_struct[3].
    # However, we do not have a direct way to compute the Weil pairing in the theta structure.
    # This means we have to get a little more creative. We propose the following:
    # For all 6 unordered pairs (Q_i, Q_j), compute Q_i + Q_j and Q_i - Q_j and successively check for spans
    # There is no difference between +- Q_i in theta coordinates (x-only coordinate arithmetic like).

    # number of points in <Q_1> == 3, reduced: {Q1} =  1
    # number of points in <Q_1, Q_2> == 9, reduced: {Q1, Q2, Q1+Q2, Q1-Q2} = 4
    # number of points in <Q_1, Q_2, Q_3> == 27, reduced: {Q1, Q2, Q3, Q1+Q2, Q1+Q3, Q2+Q3, Q1-Q2, Q1-Q3, Q2-Q3, Q1 + Q2 + Q3, Q1 + Q2 - Q3, Q1 - Q2 - Q3, Q1 - Q2 + Q3} = 13
    # number of points reduced with all 4 is 40, but we can just check that Q4 is not in the span of the first 3.

    def normalize(pt):
        coords = pt.numer
        for x in coords:
            if x != 0:
                return tuple(c / x for c in coords)  # Cast to tuple for correct hashing
        return None

    nQ1 = normalize(Q1)
    pts_normalized = set([nQ1])

    nQ2 = normalize(Q2)
    if nQ2 in pts_normalized:
        return False
    pts_normalized.add(nQ2)

    Q1_p_Q2, Q1_m_Q2 = tc_0.Normal_Add(Q1, Q2, 2)
    pts_normalized.add(normalize(Q1_p_Q2))
    pts_normalized.add(normalize(Q1_m_Q2))

    if len(pts_normalized) != 4:
        return False

    nQ3 = normalize(Q3)
    if nQ3 in pts_normalized:
        return False
    pts_normalized.add(nQ3)

    # Expand span to 13 combinations by adding ±Q3 to the previous 4 elements
    for P in [Q1, Q2, Q1_p_Q2, Q1_m_Q2]:
        P_p_Q3, P_m_Q3 = tc_0.Normal_Add(P, Q3, 2)
        pts_normalized.add(normalize(P_p_Q3))
        pts_normalized.add(normalize(P_m_Q3))

    if len(pts_normalized) != 13:
        return False

    # Check if Q4 completes the basis (not 0, not in the 3D span)
    if normalize(Q4) in pts_normalized:
        return False

    return True


def check_prod_isomorphic(E1, E2, F1, F2):
    j_in = set([E1.j_invariant(), E2.j_invariant()])
    j_targets = set([F1.j_invariant(), F2.j_invariant()])
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

    # compute codomain
    F1, F2 = codomain_curves
    rho1 = E1.isogeny(K_rho1, algorithm="factored")
    rho2 = E2.isogeny(K_rho2, algorithm="factored")

    return check_prod_isomorphic(rho1.codomain(), rho2.codomain(), F1, F2)


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
    """
    Since general addition on theta coordinates is not implemented, we need this wrapper to deal with sign ambiguities. This actually may be an issue. Attempting to guess the correct sign by checking the codomain isogeny is a bad approach since isogeny computations are expensive, but also the weil pairing is not implemented on the theta structure, so while we can check that the kernel is maximal, checking it is isotropic is more difficult.

    To recoverthis, we simply have the prover provide the correct differences of enough of the basis points to compute generators.
    """

    # With this formation of the matrix, we need only to compute B0 + v02*B2 + v03*B3 and B1 + v12*B2 + v13*B3.
    reduced_matrix, basis_perm = rref_zmod(ker_matrix)
    basis, basis_sums = reorder_basis_and_sums(basis, basis_sums, basis_perm)
    v02, v03 = int(reduced_matrix[0, 2]), int(reduced_matrix[0, 3])
    v12, v13 = int(reduced_matrix[1, 2]), int(reduced_matrix[1, 3])

    assert len(basis_sums) == 6
    # We are provided (in order) with B0 + B1, B0 + B2, B0 + B3, B1 + B2, B1 + B3, B2 + B3. We can use these to resolve sign ambiguities when building the kernel points.

    B0, B1 = basis[0], basis[1]
    v02B2 = tc_0.Mult(basis[2], v02)
    v03B3 = tc_0.Mult(basis[3], v03)
    B0_p_v02B2 = tc_0.Kxpy_xpy(v02, basis[2], basis[0], basis_sums[1])  # B0 + v02*B2
    B0_p_v03B3 = tc_0.Kxpy_xpy(v03, basis[3], basis[0], basis_sums[2])  # B0 + v03*B3
    B2_p_v03B3 = tc_0.Kxpy_xpy(v03, basis[3], basis[2], basis_sums[5])  # B2 + v03*B3
    v02B2_p_v03B3 = tc_0.Kxpy_xpy(v02, basis[2], v03B3, B2_p_v03B3)  # v02*B2 + v03*B3
    K1 = tc_0.Extended_Addition(
        B0, v02B2, v03B3, B0_p_v02B2, v02B2_p_v03B3, B0_p_v03B3
    )  # B0 + v02*B2 + v03*B3

    v12B2 = tc_0.Mult(basis[2], v12)
    v13B3 = tc_0.Mult(basis[3], v13)
    B1_p_v12B2 = tc_0.Kxpy_xpy(v12, basis[2], basis[1], basis_sums[3])  # B1 + v12*B2
    B1_p_v13B3 = tc_0.Kxpy_xpy(v13, basis[3], basis[1], basis_sums[4])  # B1 + v13*B3
    B2_p_v13B3 = tc_0.Kxpy_xpy(v13, basis[3], basis[2], basis_sums[5])  # B2 + v13*B3
    v12B2_p_v13B3 = tc_0.Kxpy_xpy(v12, basis[2], v13B3, B2_p_v13B3)  # v12*B2 + v13*B3
    K2 = tc_0.Extended_Addition(
        B1, v12B2, v13B3, B1_p_v12B2, v12B2_p_v13B3, B1_p_v13B3
    )  # B1 + v12*B2 + v13*B3

    return K1, K2


def correct_tc_for_prod(tc_0):
    """
    returns None if not an elliptic product, otherwise returns the tuple of elliptic curves (E1, E2) such that the theta structure is a product of theta structures on E1 and E2
    """
    K = tc_0.field
    tc_0_coords = tc_0.numer
    zeta_4 = K.gen()
    assert zeta_4**2 == -1
    is_ell_prod = Is_Elliptic_product(tc_0_coords)
    if not is_ell_prod[0]:
        return None

    if is_ell_prod[1]:  # already split.
        return is_ell_prod[1]
    else:
        i = is_ell_prod[2]  # (i,j) is zero even theta.
        j = is_ell_prod[3]

    if (i, j) == (0, 0):
        tc_0_coords[2] *= zeta_4
        tc_0_coords[3] *= zeta_4
    is_ell_prod = Is_Elliptic_product(tc_0_coords)
    if is_ell_prod[1]:
        return tc_0_coords
    else:
        i = is_ell_prod[2]  # (i,j) is zero even theta.
        j = is_ell_prod[3]
    if i != 0 and j == 0:
        assert i != 0
        tc_0_coords = Theta_Hadamard(tc_0_coords)

    is_ell_prod = Is_Elliptic_product(tc_0_coords)
    if is_ell_prod[1]:
        return tc_0_coords
    else:
        i = is_ell_prod[2]  # (i,j) is zero even theta.
        j = is_ell_prod[3]
    assert j != 0
    if j == 1:
        tc_0_coords[1], tc_0_coords[3] = (tc_0_coords[3], tc_0_coords[1])
    elif j == 2:
        tc_0_coords[2], tc_0_coords[3] = (tc_0_coords[3], tc_0_coords[2])

    is_ell_prod = Is_Elliptic_product(tc_0_coords)
    if is_ell_prod[1]:
        return tc_0_coords
    else:
        i = is_ell_prod[2]  # (i,j) is zero even theta.
        j = is_ell_prod[3]
    assert i == 0 and j == 3
    tc_0_coords[1] *= zeta_4
    tc_0_coords[2] *= zeta_4

    is_ell_prod = Is_Elliptic_product(tc_0_coords)
    assert is_ell_prod[1]

    return tc_0_coords


def has_codomain_two_dim(ker_matrix, basis, basis_sums, M, domain: ThetaStructure, codomain_curves):
    "Assumes M = 3**e for some e. ker_matrix is 2x4 matrix of coefficients in the basis. codomain curves are E1, E2 in the product structure that we want to have as codomain."
    if not is_full_rank(ker_matrix, M):
        return False

    # Converting basis to the correct type:
    K = domain.base_ring()
    tc_0 = NullCoord(domain.null_point().coords(), 1, K)
    basis = [Coord(pt.coords(), 1, K) for pt in basis]
    basis_sums = [Coord(pt.coords(), 1, K) for pt in basis_sums]

    K1, K2 = theta_matrix_basis_to_pts(ker_matrix, basis, basis_sums, tc_0, M)
    try:
        # The basis check and full-rank matrix already imply exact M-order here.
        A = get_codomain_from_tc_odd(tc_0, [K1, K2], M, perform_checks=False)
    except AssertionError:
        raise ValueError("Isogeny passes through product, which is not implemented yet. Try again!")

    # Now convert A to product of curves
    tc_prod = correct_tc_for_prod(A)
    if tc_prod is None:
        return False  # codomain not a product

    tc_F1 = [tc_prod[0], tc_prod[1]]
    tc_F2 = [tc_prod[0], tc_prod[2]]
    lm_F1 = Lv2tnp_to_Legendre(tc_F1)[0]
    lm_F2 = Lv2tnp_to_Legendre(tc_F2)[0]
    F1 = Legendre_to_Elliptic(lm_F1)
    F2 = Legendre_to_Elliptic(lm_F2)
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

    _, _, _, computed_A, computed_images = mapping_E0xE1_to_A_even(
        E1, E2, above_ker_points, N, points
    )
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
