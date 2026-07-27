from collections import deque
from copy import copy

from vendors.EllEll_Isogeny_Sage.func_isogeny import CodOne, EvalOne, Product_power_lambda
from vendors.Theta_SageMath.theta_structures.product_structure import ProductThetaStructure
from vendors.Theta_SageMath.theta_structures.dimension_two import ThetaPoint, ThetaStructure
from vendors.Theta_SageMath.theta_structures.couple_point import CouplePoint
from vendors.Theta_SageMath.theta_isogenies.morphism import Morphism
from vendors.Theta_SageMath.theta_isogenies.gluing_isogeny import GluingThetaIsogeny
from vendors.Theta_SageMath.theta_isogenies.isogeny import ThetaIsogeny
from vendors.Theta_SageMath.utilities.strategy import optimised_strategy

from vendors.EllEll_Isogeny_Sage.class_theta import Coord, NullCoord
from vendors.EllEll_Isogeny_Sage.func_elliptic import (
    Decomp_degree,
    Elliptic_to_Legendre,
    Elliptic_to_Legendre_with_basis,
    Is_Elliptic_product,
    Legendre_to_lv2tnp,
    Product_theta,
)
from vendors.EllEll_Isogeny_Sage.func_for_attack import Attack_main, Construct_pt
from sage.all import gcd, gen, identity_matrix, is_prime, matrix, vector

# TODO: Unify dependencies to use more-or-less one tc rep.


def product_isomorphisms(F0, F1, G0, G1):
    """Returns the set of isomorphisms from F0xF1 to G0xG1, assuming they are isomorphic."""
    assert set([F0.j_invariant(), F1.j_invariant()]) == set([G0.j_invariant(), G1.j_invariant()])
    if F0.j_invariant() == G0.j_invariant() and F1.j_invariant() == G1.j_invariant():
        for iso_0 in F0.isomorphisms(G0):
            for iso_1 in F1.isomorphisms(G1):

                def composed_iso(domain_pt: CouplePoint, _iso_0=iso_0, _iso_1=iso_1):
                    return CouplePoint(_iso_0(domain_pt[0]), _iso_1(domain_pt[1]))

                yield composed_iso
    elif F0.j_invariant() == G1.j_invariant() and F1.j_invariant() == G0.j_invariant():
        for iso_0 in F0.isomorphisms(G1):
            for iso_1 in F1.isomorphisms(G0):

                def composed_iso(domain_pt: CouplePoint, _iso_0=iso_0, _iso_1=iso_1):
                    return CouplePoint(_iso_1(domain_pt[1]), _iso_0(domain_pt[0]))

                yield composed_iso
    raise ValueError("inputs are not isomorphic")


def tc_isomorphisms(struct1: ThetaStructure, struct2: ThetaStructure):
    """
    returns the set of isomorphisms from struct1 to struct2, assuming they are isomorphic.
    """
    F = struct1.base_ring()
    if F != struct2.base_ring():
        raise ValueError("Theta structures must be defined over the same base field.")

    i_val = F.gen()
    start_pt = struct1.coords()
    target_pt = struct2.coords()

    isomorphisms = []

    def normalize(pt):
        for x in pt:
            if x != 0:
                inv = F(1 / x)
                return tuple(c * inv for c in pt)
        return pt

    target_norm = normalize(target_pt)
    if normalize(start_pt) == target_norm:
        return True, lambda pt: pt

    def H1(a, b, c, d):
        return (a + c, b + d, a - c, b - d)

    def H2(a, b, c, d):
        return (a + b, a - b, c + d, c - d)

    def S1(a, b, c, d):
        return (a, b * i_val, c, d * i_val)

    def S2(a, b, c, d):
        return (a, b, c * i_val, d * i_val)

    def CZ(a, b, c, d):
        return (a, b, c, -d)

    generators = [H1, H2, S1, S2, CZ]
    visited = {normalize(start_pt)}

    # queue now stores tuples of (current_point, list_of_applied_generators)
    queue = deque([(start_pt, [])])

    while queue:
        curr, path = queue.popleft()
        for gen in generators:
            nxt = gen(*curr)
            norm_nxt = normalize(nxt)

            # The exact sequence of operations that led to this point
            new_path = path + [gen]

            if norm_nxt == target_norm:
                # Build a mapping function based on the discovered sequence
                def isomorphism_map(pt: ThetaPoint, seq=copy(new_path)) -> ThetaPoint:
                    assert pt.parent() == struct1
                    res = pt.coords()
                    for g in seq:
                        res = g(*res)
                    return ThetaPoint(struct2, res)

                yield isomorphism_map

            if norm_nxt not in visited:
                visited.add(norm_nxt)
                queue.append((nxt, new_path))

    return isomorphisms


def get_isomorphism(A, B):
    """Returns an isomorphism from PPAS A to B, assuming they are isomorphic."""
    if isinstance(A, ProductThetaStructure) and isinstance(B, ProductThetaStructure):
        return next(product_isomorphisms(A[0], A[1], B[0], B[1]))
    elif isinstance(A, ThetaStructure) and isinstance(B, ThetaStructure):
        return next(tc_isomorphisms(A, B))
    raise ValueError("Unsupported types for isomorphism")


def torsion_mapping_E0xE1_to_A_odd(E0, E1, ker, d, basis, f, perform_checks=True, bypass_legendre=False, legendre_syms=None):
    """
    Computes the action of an (d, d)-isogeny from E0 x E1 -> A on a given f-torsion basis.
    d must be odd.
    """
    K = E0.base_ring()
    if perform_checks:
        assert d % 2 == 1, "M must be odd for this function to work."
        p = K.characteristic()
        assert E0.is_supersingular() and E1.is_supersingular()
        assert (p + 1) % d == 0, "d-torsion must be rational for this function to work."
        assert (p + 1) % f == 0, "f-torsion must be rational for this function to work."
        assert gcd(d, f) == 1, "d and f must be coprime for this function to work."

    if bypass_legendre:
        lm_0, lm_1 = legendre_syms
    else:
        lm_0, E0_L, iso_E0_E0L = Elliptic_to_Legendre(E0)
        lm_1, E1_L, iso_E1_E1L = Elliptic_to_Legendre(E1)

    kernel_lambda = [
        (iso_E0_E0L(ker[0][0]), iso_E1_E1L(ker[0][1])),
        (iso_E0_E0L(ker[1][0]), iso_E1_E1L(ker[1][1])),
    ]
    lv2tnp_E0, sq_rt_lm_0, sq_rt_lmm1_0 = Legendre_to_lv2tnp(lm_0)
    lv2tnp_E1, sq_rt_lm_1, sq_rt_lmm1_1 = Legendre_to_lv2tnp(lm_1)
    tc_0_co = Product_theta(lv2tnp_E0, lv2tnp_E1)
    tc_0 = NullCoord([K(tc_0_co[i]) for i in range(0, 4)], 1, K)
    ell_data = [
        lm_0,
        sq_rt_lm_0,
        sq_rt_lmm1_0,
        lv2tnp_E0,
        lm_1,
        sq_rt_lm_1,
        sq_rt_lmm1_1,
        lv2tnp_E1,
    ]
    f_1 = kernel_lambda[0]
    f_2 = kernel_lambda[1]

    x_1 = [iso_E0_E0L(basis[0][0]), iso_E1_E1L(basis[0][1])]
    y_1 = [iso_E0_E0L(basis[1][0]), iso_E1_E1L(basis[1][1])]

    tc_f1 = Construct_pt(ell_data, f_1, K)
    tc_f2 = Construct_pt(ell_data, f_2, K)
    tc_f12 = Construct_pt(ell_data, [f_1[0] + f_2[0], f_1[1] + f_2[1]], K)
    tc_x_1 = Construct_pt(ell_data, x_1, K)
    tc_x_1pf1 = Construct_pt(ell_data, [x_1[0] + f_1[0], x_1[1] + f_1[1]], K)
    tc_x_1pf2 = Construct_pt(ell_data, [x_1[0] + f_2[0], x_1[1] + f_2[1]], K)
    tc_y_1 = Construct_pt(ell_data, y_1, K)
    tc_y_1pf1 = Construct_pt(ell_data, [y_1[0] + f_1[0], y_1[1] + f_1[1]], K)
    tc_y_1pf2 = Construct_pt(ell_data, [y_1[0] + f_2[0], y_1[1] + f_2[1]], K)

    x_2 = [iso_E0_E0L(basis[2][0]), iso_E1_E1L(basis[2][1])]
    y_2 = [iso_E0_E0L(basis[3][0]), iso_E1_E1L(basis[3][1])]
    tc_x_2 = Construct_pt(ell_data, x_2, K)
    tc_x_2pf1 = Construct_pt(ell_data, [x_2[0] + f_1[0], x_2[1] + f_1[1]], K)
    tc_x_2pf2 = Construct_pt(ell_data, [x_2[0] + f_2[0], x_2[1] + f_2[1]], K)
    tc_y_2 = Construct_pt(ell_data, y_2, K)
    tc_y_2pf1 = Construct_pt(ell_data, [y_2[0] + f_1[0], y_2[1] + f_1[1]], K)
    tc_y_2pf2 = Construct_pt(ell_data, [y_2[0] + f_2[0], y_2[1] + f_2[1]], K)

    assert Is_Elliptic_product(tc_0.numer)[0]
    ext_kernel_basis = (tc_f1, tc_f2, tc_f12)
    ext_x_1 = (tc_x_1, tc_x_1pf1, tc_x_1pf2)
    ext_y_1 = (tc_y_1, tc_y_1pf1, tc_y_1pf2)
    ext_x_2 = (tc_x_2, tc_x_2pf1, tc_x_2pf2)
    ext_y_2 = (tc_y_2, tc_y_2pf1, tc_y_2pf2)
    # TODO: reduce this to a single call to another helper function.
    tc_0_co, ext_x_1_img, ext_y_1_img, _ = Attack_main(
        d,
        f,
        tc_0,
        ext_kernel_basis,
        ext_x_1,
        ext_y_1,
    )
    tc_0_co_x, ext_x_2_img, ext_y_2_img, _ = Attack_main(
        d,
        f,
        tc_0,
        ext_kernel_basis,
        ext_x_2,
        ext_y_2,
    )

    assert tc_0_co_x.Is_same_proj(tc_0_co)
    domain_basis = [
        x_1,
        y_1,
        x_2,
        y_2,
    ]
    codomain_basis = [
        ext_x_1_img,
        ext_y_1_img,
        ext_x_2_img,
        ext_y_2_img,
    ]
    assert tc_0_co.denom == 1
    # tc_0_co = ThetaStructure(tc_0_co.numer)  # codomains theta null coordinate.
    return (E0_L, E1_L, domain_basis, tc_0_co, codomain_basis)


def mapping_E0xE1_to_A_even(E0, E1, above_ker, d, pts_to_eval, perform_checks=True):
    """
    Computes the action of an (d, d)-isogeny from E0 x E1 -> A on a given f-torsion basis.
    d must be a power of 2.
    """
    if perform_checks:
        assert d & (d - 1) == 0, "d must be a power of 2 for this function to work."
        assert all(isinstance(pt, CouplePoint) for pt in pts_to_eval)
        assert len(above_ker) == 2 and all(isinstance(pt, CouplePoint) for pt in above_ker)
    n = d.bit_length() - 1

    K = E0.base_ring()
    strategy = optimised_strategy(n)
    T1, T2 = above_ker

    # Bookkeeping for optimal strategy
    strat_idx = 0
    level = [0]
    ker = (T1, T2)
    kernel_elements = [ker]
    Th = None

    # track coprime basis
    pts_img = copy(pts_to_eval)

    for k in range(n):
        prev = sum(level)
        ker = kernel_elements[-1]

        while prev != (n - 1 - k):
            level.append(strategy[strat_idx])

            # Perform the doublings
            T1 = ker[0].double_iter(strategy[strat_idx])
            T2 = ker[1].double_iter(strategy[strat_idx])

            ker = (T1, T2)

            # Update kernel elements and bookkeeping variables
            kernel_elements.append(ker)
            prev += strategy[strat_idx]
            strat_idx += 1

        # Compute the codomain from the 8-torsion
        T1, T2 = ker
        if k == 0:
            phi = GluingThetaIsogeny(T1, T2)
        elif k == n - 2:
            # The next isogeny will be a splitting isogeny, so we know we
            # will have one of a,b,c,d = 0. So at this point switch to
            # dual theta coordinate
            phi = ThetaIsogeny(Th, T1, T2, hadamard=(False, False))
        elif k == n - 1:
            # Compute the dual isogeny, remembering that we switched to
            # dual theta coordinates at the previous step.
            # We output dual theta coordinates on the product, change
            # to hadamard=(True, True) to output standard coordinates;
            # this does not change the conversion back to Montgomery
            # coordinates so we might as well save an Hadamard
            # transform anyway
            phi = ThetaIsogeny(Th, T1, T2, hadamard=(True, False))
        else:
            phi = ThetaIsogeny(Th, T1, T2)

        # Update the chain of isogenies
        Th = phi.codomain()
        pts_img = [phi(pt) for pt in pts_img]

        # Remove elements from list
        kernel_elements.pop()
        level.pop()

        # Push through points for the next step
        kernel_elements = [(phi(T1), phi(T2)) for T1, T2 in kernel_elements]

    tc_0_co = Th
    return (E0, E1, pts_to_eval, tc_0_co, pts_img)


# def evaluate_point_from_torsion(pt, domain_basis, codomain_basis, M, d):
#     """
#     Evaluates the image of a point under the isogeny defined by the torsion mapping, given the point's coordinates in the domain basis.
#     """
#     alpha, beta = get_coefficients_wrt(pt, domain_basis[0], domain_basis[1], M)
#     gamma, delta = get_coefficients_wrt(pt, domain_basis[2], domain_basis[3], M)
#     return (
#         alpha * codomain_basis[0]
#         + beta * codomain_basis[1]
#         + gamma * codomain_basis[2]
#         + delta * codomain_basis[3]
#     )


def compute_zeta_4(F):
    X = gen(F["X"])
    f = X**2 + 1
    zeta_4 = f.roots()[1][0]
    return zeta_4


def _Kxpy_xpy_shared(tc_0, tc_x, computations):
    """
    Run ``Kxpy_xpy`` ladders with the same ``x`` and bit length.

    The ladders have the same sequence of doublings even when their scalars
    differ, so sharing that sequence preserves their separate affine lifts.
    """
    bit_sequences = [(k - 1).digits(2) for k, _, _ in computations]
    assert all(k > 5 for k, _, _ in computations)
    assert all(len(bits) == len(bit_sequences[0]) for bits in bit_sequences)
    assert all(bits[-1] == 1 for bits in bit_sequences)
    X = tc_x
    Y = [tc_xpy for _, _, tc_xpy in computations]
    Z = [tc_y for _, tc_y, _ in computations]

    for index in range(len(bit_sequences[0]) - 1):
        dX = tc_0.Double(X)
        for j, bits in enumerate(bit_sequences):
            if bits[index] == 1:
                Y[j] = tc_0.Diff_Add(X, Y[j], Z[j])
            else:
                assert bits[index] == 0
                Z[j] = tc_0.Diff_Add(X, Z[j], Y[j])
        X = dX

    return tuple(tc_0.Diff_Add(X, y, z) for y, z in zip(Y, Z))


def get_codomain_from_tc_odd(tc_0, ker, d, perform_checks=True):
    """
    Similar to get_torsion_mapping, but only returns the codomain theta null coordinate of B such that A -> B under the d-isogeny generated by kernel.
    """
    # kernel_lambda = [
    #     (iso_E0_E0L(ker[0][0]), iso_E1_E1L(ker[0][1])),
    #     (iso_E0_E0L(ker[1][0]), iso_E1_E1L(ker[1][1])),
    # ]
    # lv2tnp_E0, sq_rt_lm_0, sq_rt_lmm1_0 = Legendre_to_lv2tnp(lm_0)
    # lv2tnp_E1, sq_rt_lm_1, sq_rt_lmm1_1 = Legendre_to_lv2tnp(lm_1)
    # tc_0_co = Product_theta(lv2tnp_E0, lv2tnp_E1)
    # tc_0 = NullCoord([K(tc_0_co[i]) for i in range(0, 4)], 1, K)
    # ell_data = [
    #     lm_0,
    #     sq_rt_lm_0,
    #     sq_rt_lmm1_0,
    #     lv2tnp_E0,
    #     lm_1,
    #     sq_rt_lm_1,
    #     sq_rt_lmm1_1,
    #     lv2tnp_E1,
    # ]
    # f_1 = kernel_lambda[0]
    # f_2 = kernel_lambda[1]

    # x_1 = [iso_E0_E0L(basis[0][0]), iso_E1_E1L(basis[0][1])]
    # y_1 = [iso_E0_E0L(basis[1][0]), iso_E1_E1L(basis[1][1])]

    # tc_f1 = Construct_pt(ell_data, f_1, K)
    # tc_f2 = Construct_pt(ell_data, f_2, K)
    # tc_f12 = Construct_pt(ell_data, [f_1[0] + f_2[0], f_1[1] + f_2[1]], K)
    tc_f1 = ker[0]
    tc_f2 = ker[1]
    tc_f12 = tc_0.Normal_Add(tc_f1, tc_f2, 1)
    # tc_x_1 = Construct_pt(ell_data, x_1, K)
    # tc_x_1pf1 = Construct_pt(ell_data, [x_1[0] + f_1[0], x_1[1] + f_1[1]], K)
    # tc_x_1pf2 = Construct_pt(ell_data, [x_1[0] + f_2[0], x_1[1] + f_2[1]], K)
    # tc_y_1 = Construct_pt(ell_data, y_1, K)
    # tc_y_1pf1 = Construct_pt(ell_data, [y_1[0] + f_1[0], y_1[1] + f_1[1]], K)
    # tc_y_1pf2 = Construct_pt(ell_data, [y_1[0] + f_2[0], y_1[1] + f_2[1]], K)

    # x_2 = [iso_E0_E0L(basis[2][0]), iso_E1_E1L(basis[2][1])]
    # y_2 = [iso_E0_E0L(basis[3][0]), iso_E1_E1L(basis[3][1])]
    # tc_x_2 = Construct_pt(ell_data, x_2, K)
    # tc_x_2pf1 = Construct_pt(ell_data, [x_2[0] + f_1[0], x_2[1] + f_1[1]], K)
    # tc_x_2pf2 = Construct_pt(ell_data, [x_2[0] + f_2[0], x_2[1] + f_2[1]], K)
    # tc_y_2 = Construct_pt(ell_data, y_2, K)
    # tc_y_2pf1 = Construct_pt(ell_data, [y_2[0] + f_1[0], y_2[1] + f_1[1]], K)
    # tc_y_2pf2 = Construct_pt(ell_data, [y_2[0] + f_2[0], y_2[1] + f_2[1]], K)

    # assert Is_Elliptic_product(tc_0.numer)[0]
    ext_kernel_basis = (tc_f1, tc_f2, tc_f12)
    # ext_x_1 = (tc_x_1, tc_x_1pf1, tc_x_1pf2)
    # ext_y_1 = (tc_y_1, tc_y_1pf1, tc_y_1pf2)
    # ext_x_2 = (tc_x_2, tc_x_2pf1, tc_x_2pf2)
    # ext_y_2 = (tc_y_2, tc_y_2pf1, tc_y_2pf2)
    # TODO: reduce this to a single call to another helper function.
    (tc_f1,tc_f2,tc_f12)=ext_kernel_basis
    # (tc_x,tc_xpf1,tc_xpf2)=ext_x
    # (tc_y,tc_ypf1,tc_ypf2)=ext_y
    if perform_checks:
        assert(tc_0.Is_order(tc_f1  ,d))
        assert(tc_0.Is_order(tc_f2  ,d))
        assert(tc_0.Is_order(tc_f12 ,d))
        assert(tc_0.Is_same_proj(tc_0.Mult(tc_0,2)))
    # assert(tc_0.Is_order(tc_x   ,N_B))
    # assert(tc_0.Is_order(tc_xpf1,N_A*N_B))
    # assert(tc_0.Is_order(tc_xpf2,N_A*N_B))
    # assert(tc_0.Is_order(tc_y   ,N_B))
    # assert(tc_0.Is_order(tc_ypf1,N_A*N_B))
    # assert(tc_0.Is_order(tc_ypf2,N_A*N_B))
    fac=Decomp_degree(d)
    # print("isogeny chain:",fac)
    s=1
    for i in range(0,len(fac)):
        l=fac[i]
        assert(is_prime(l))
        k=d//(s*l)
        assert(s*l*k==d)
        # print("ell=",l)
        if i!=0: #if not the first step.
            tc_f12=tc_0.Normal_Add(tc_f1,tc_f2,1)
        #construct kernel e_1,e_2,e_1+e_2.
        is_terminal = i == len(fac) - 1
        if is_terminal:
            tc_e1 =tc_0.Mult(tc_f1 ,k)
            tc_e2 =tc_0.Mult(tc_f2 ,k)
        elif k > 5 and len((k - 1).digits(2)) == len(k.digits(2)):
            # Compute [k]f_i, f_j + [k]f_i, and [k+1]f_i together.
            # They share the doubled X spine; their Y/Z additions stay separate.
            tc_e1, tc_f2pe1, tc_f1pe1 = _Kxpy_xpy_shared(
                tc_0,
                tc_f1,
                (
                    (k, tc_0, tc_f1),
                    (k, tc_f2, tc_f12),
                    (k + 1, tc_0, tc_f1),
                ),
            )
            tc_e2, tc_f1pe2, tc_f2pe2 = _Kxpy_xpy_shared(
                tc_0,
                tc_f2,
                (
                    (k, tc_0, tc_f2),
                    (k, tc_f1, tc_f12),
                    (k + 1, tc_0, tc_f2),
                ),
            )
        else:
            tc_e1 =tc_0.Mult(tc_f1 ,k)
            tc_e2 =tc_0.Mult(tc_f2 ,k)
            tc_f1pe1=tc_0.Mult(tc_f1,k+1)
            tc_f1pe2=tc_0.Kxpy_xpy(k,tc_f2,tc_f1,tc_f12)
            tc_f2pe1=tc_0.Kxpy_xpy(k,tc_f1,tc_f2,tc_f12)
            tc_f2pe2=tc_0.Mult(tc_f2,k+1)
        tc_e12=tc_0.Mult(tc_f12,k)
        tc_e1.order=l
        tc_e2.order=l
        tc_e12.order=l
        #assert(tc_0.Is_order(tc_e1  ,l))
        #assert(tc_0.Is_order(tc_e2  ,l))
        #assert(tc_0.Is_order(tc_e12 ,l))
        #assert(tc_0.Is_order(tc_f1  ,k*l))
        #assert(tc_0.Is_order(tc_f2  ,k*l))
        #assert(tc_0.Is_order(tc_f12 ,k*l))
        #assert(tc_0.Is_order(tc_x   ,N_B))
        #assert(tc_0.Is_order(tc_y   ,N_B))
        # if i==0:
        #     tc_xpe1 =tc_0.Kxpy_xpy(k,tc_f1,tc_x,tc_xpf1)#x+e_1
        #     tc_xpe2 =tc_0.Kxpy_xpy(k,tc_f2,tc_x,tc_xpf2)#x+e_2
        #     tc_ype1 =tc_0.Kxpy_xpy(k,tc_f1,tc_y,tc_ypf1)#y+e_1
        #     tc_ype2 =tc_0.Kxpy_xpy(k,tc_f2,tc_y,tc_ypf2)#y+e_2
        # if i!=0:
        #     tc_xpe1 =tc_0.Normal_Add(tc_x,tc_e1,1)#x+e_1
        #     tc_xpe2 =tc_0.Compatible_Add(tc_x,tc_e2,tc_xpe1,tc_e12)#x+e_2
        #     tc_ype1 =tc_0.Normal_Add(tc_y,tc_e1,1)#y+e_1
        #     tc_ype2 =tc_0.Compatible_Add(tc_y,tc_e2,tc_ype1,tc_e12)#y+e_2
        #assert(tc_0.Is_order(tc_xpe1,l*N_B))
        #assert(tc_0.Is_order(tc_xpe2,l*N_B))
        #assert(tc_0.Is_order(tc_ype1,l*N_B))
        #assert(tc_0.Is_order(tc_ype2,l*N_B))
        basis  =[tc_e1,tc_e2   ,tc_e12  ]
        # x_list =[tc_x ,tc_xpe1 ,tc_xpe2 ]
        # y_list =[tc_y ,tc_ype1 ,tc_ype2 ]
        #-----------------------------------------------------------------------------------------
        tc_cd0=CodOne(tc_0,basis)
        if is_terminal:
            tc_0 = tc_cd0
            break

        f1_list=[tc_f1,tc_f1pe1,tc_f1pe2]
        f2_list=[tc_f2,tc_f2pe1,tc_f2pe2]
        lmd_data=Product_power_lambda(basis)
        tc_f1=EvalOne(tc_0,basis,f1_list,lmd_data)
        tc_f2=EvalOne(tc_0,basis,f2_list,lmd_data)
        # tc_x =EvalOne(tc_0,basis,x_list ,lmd_data)
        # tc_y =EvalOne(tc_0,basis,y_list ,lmd_data)
        tc_0 =tc_cd0
        s*=l
        #assert(tc_0.Is_order(tc_x,N_B))
        #assert(tc_0.Is_order(tc_y,N_B))
        #assert(tc_0.Is_order(tc_f1,k))
        #assert(tc_0.Is_order(tc_f2,k))
    #=====================================
    # assert(Is_Elliptic_product(tc_0.numer)[0])
    # assert(tc_0.Is_same_proj(tc_f1))
    return tc_0


def get_codomain_from_E0xE1_even(E0, E1, above_ker, d, perform_checks=True):
    _, _, _, tc_0_co, _ = mapping_E0xE1_to_A_even(E0, E1, above_ker, d, None, perform_checks)
    return tc_0_co
