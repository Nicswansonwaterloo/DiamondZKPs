from sage.all import Zmod, discrete_log, randint, vector

from helpers.ec_utils import randomize_basis
from helpers.helpers import normalize_and_hash
from helpers.montgomery_helpers import (
    is_supersingular_and_correct_characteristic_kummer,
    kummer_basis_from_points,
    x_only_linear_comb,
    x_only_is_basis_cube,
)
from helpers.two_dim_utils import get_points_above_kernel
from helpers.two_dim_wrappers import mapping_E0xE1_to_A_even
from vendors.Kummer_Isogeny.kummer_isogeny import KummerLineIsogeny
from vendors.Kummer_Isogeny.kummer_line import KummerLine
from vendors.SQIsign2DSquare.rii import RanIso, make_precomputed_values
from vendors.Theta_SageMath.theta_isogenies.isomorphism import SplittingIsomorphism
from vendors.Theta_SageMath.theta_structures.couple_point import CouplePoint
from vendors.Theta_SageMath.theta_structures.split_structure import SplitThetaStructure
from vendors.Theta_SageMath.utilities.supersingular import (
    compute_linearly_independent_point,
    torsion_basis,
)
from vendors.Theta_SageMath.utilities.utils import speed_up_sagemath

NUM_CHALLENGES = 5


def key_gen(params):
    """Generate the non-smooth Kani diamond and compatible C-torsion bases."""
    p, N, e2, C, e3, c, A, B, _, Fp2 = params

    # Generate the public Kani diamond.
    global_data = make_precomputed_values(p, e2, e3, Fp2)
    ran_iso = RanIso(A, global_data)
    E0 = ran_iso.E0
    EA = ran_iso.EA
    EB = ran_iso.EB
    EAB = ran_iso.EAB
    K0, K1 = ran_iso.kernel
    above_kernel = get_points_above_kernel(K0, K1, N)

    # Precompute compatible C-torsion bases on E0 and EAB.
    P0, Q0 = global_data.E0_data.OddTorsionBases[0]
    RAB, SAB = torsion_basis(EAB, C)
    product_basis = [
        CouplePoint(P0, EAB(0)),
        CouplePoint(Q0, EAB(0)),
        CouplePoint(E0(0), RAB),
        CouplePoint(E0(0), SAB),
    ]
    basis_images = [ran_iso.Phi(P) for P in product_basis]
    sum_images = [ran_iso.Phi(product_basis[0] + P) for P in product_basis[1:]]

    corrected_images = [basis_images[0]]
    # Corrected in the senses of the product-Kummer signs using the three additional sums.
    for image, sum_image in zip(basis_images[1:], sum_images):
        components = [image[0], image[1]]
        for i in range(2):
            if (
                basis_images[0][i] + components[i] != sum_image[i]
                and basis_images[0][i] + components[i] != -sum_image[i]
            ):
                components[i] = -components[i]
        corrected_images.append(CouplePoint(*components))
    basis_images = corrected_images

    # As a map from E0 to EAB, we want Phi' to be the composition of an A isogeny followed by a B isogeny.
    source_pairing = P0.weil_pairing(Q0, C)
    pairing_0 = basis_images[0][0].weil_pairing(basis_images[1][0], C)
    pairing_1 = basis_images[0][1].weil_pairing(basis_images[1][1], C)
    if pairing_0 == source_pairing**B and pairing_1 == source_pairing**A:
        basis_images = [CouplePoint(P[1], P[0]) for P in basis_images]
    elif pairing_0 != source_pairing**A or pairing_1 != source_pairing**B:
        raise ValueError("Could not identify the A and B factors.")

    zeta_AB = RAB.weil_pairing(SAB, C)
    compatible_AB_basis = []
    for target in (basis_images[0][0], basis_images[1][0]):
        pairing_R = basis_images[2][0].weil_pairing(target, C)
        pairing_S = basis_images[3][0].weil_pairing(target, C)
        b = discrete_log(pairing_R, zeta_AB, ord=C)
        a = -discrete_log(pairing_S, zeta_AB, ord=C)
        compatible_AB_basis.append(a * RAB + b * SAB)
    PAB, QAB = compatible_AB_basis

    E0_kum = KummerLine(E0)
    EAB_kum = KummerLine(EAB)
    # Special basis such that the Kummer images of the two compatible C-torsion bases are in the same order.
    E0_C_basis = kummer_basis_from_points(E0_kum, P0, Q0)
    EAB_C_basis = kummer_basis_from_points(EAB_kum, PAB, QAB)
    assert x_only_is_basis_cube(*EAB_C_basis, C, EAB)

    # Keep the deliberately bloated witness. See the prover for how to reduce it to a more compact form.
    sk = (ran_iso.kernel, above_kernel, (E0_C_basis, EAB_C_basis), ran_iso)
    pk = (E0, EA, EB, EAB)
    return sk, pk


def prover(params, sk, pk):
    p, N, _, C, _, _, A, B, _, _ = params
    _, above_kernel, compatible_c_bases, _ = sk
    (xP0, xQ0, xPQ0), (xPAB, xQAB, xPQAB) = compatible_c_bases
    E0_kum = xP0.parent()
    EAB_kum = xPAB.parent()

    # Sample the two compatible C-kernels with the same scalar.
    C_kernel_vector = vector(Zmod(C), [1, randint(0, C - 1)])
    s = C_kernel_vector[1]
    xK_C = xQ0.ladder_3_pt(xP0, xPQ0, s)
    xK_ABC = xQAB.ladder_3_pt(xPAB, xPQAB, s)
    phi_C = KummerLineIsogeny(E0_kum, xK_C, C)
    psi_ABC = KummerLineIsogeny(EAB_kum, xK_ABC, C)
    EC_kum = phi_C.codomain()
    EABC_kum = psi_ABC.codomain()
    EC = EC_kum.curve()
    EABC = EABC_kum.curve()

    # Lift only the N-torsion data needed by the two-dimensional evaluator.
    T0, T1 = above_kernel
    T0_C = phi_C(E0_kum(T0[0])).curve_point()
    T1_C = phi_C(E0_kum(T1[0])).curve_point()
    T01_C = phi_C(E0_kum(T0[0] + T1[0])).curve_point()
    if T0_C + T1_C != T01_C and T0_C + T1_C != -T01_C:
        T1_C = -T1_C

    T0_ABC = psi_ABC(EAB_kum(T0[1])).curve_point()
    T1_ABC = psi_ABC(EAB_kum(T1[1])).curve_point()
    T01_ABC = psi_ABC(EAB_kum(T0[1] + T1[1])).curve_point()
    if T0_ABC + T1_ABC != T01_ABC and T0_ABC + T1_ABC != -T01_ABC:
        T1_ABC = -T1_ABC

    phi_prime_above_kernel = (
        CouplePoint(T0_C, T0_ABC),
        CouplePoint(T1_C, T1_ABC),
    )

    # Randomize a basis containing ker(hat(phi_C)).
    K_phi_C_dual = phi_C(xQ0).curve_point()
    independent_C = compute_linearly_independent_point(
        EC, K_phi_C_dual, C, x_start=randint(0, p - 1)
    )
    (PC, QC), _, dual_kernel_vector = randomize_basis(
        [K_phi_C_dual, independent_C], C, sk_vector=[1, 0]
    )

    K_psi_ABC_dual = psi_ABC(xQAB).curve_point()
    independent_ABC = compute_linearly_independent_point(
        EABC, K_psi_ABC_dual, C, x_start=randint(0, p - 1)
    )
    temporary_PABC = K_psi_ABC_dual
    temporary_QABC = independent_ABC

    zero_C = EC(0)
    zero_ABC = EABC(0)
    product_basis = [
        CouplePoint(PC, zero_ABC),
        CouplePoint(QC, zero_ABC),
        CouplePoint(zero_C, temporary_PABC),
        CouplePoint(zero_C, temporary_QABC),
    ]
    points_to_evaluate = [
        *product_basis,
        product_basis[0] + product_basis[1],
        product_basis[0] + product_basis[2],
        product_basis[0] + product_basis[3],
    ]

    _, _, _, codomain, images = mapping_E0xE1_to_A_even(
        EC,
        EABC,
        phi_prime_above_kernel,
        N,
        points_to_evaluate,
    )

    # Split the final theta structure and resolve the signs of the four basis
    # images using the three additional sums.
    splitting_iso = SplittingIsomorphism(codomain)
    split_product = SplitThetaStructure(splitting_iso.codomain())
    images = [split_product(splitting_iso(theta_image)) for theta_image in images]
    basis_images = images[:4]
    sum_images = images[4:]

    corrected_images = [basis_images[0]]
    for image, sum_image in zip(basis_images[1:], sum_images):
        components = [image[0], image[1]]
        for i in range(2):
            if (
                basis_images[0][i] + components[i] != sum_image[i]
                and basis_images[0][i] + components[i] != -sum_image[i]
            ):
                components[i] = -components[i]
        corrected_images.append(CouplePoint(*components))
    basis_images = corrected_images

    # Order the split factors as EAC and EBC using their pairing degrees.
    EAC, EBC = split_product.curves()
    source_pairing = PC.weil_pairing(QC, C)
    pairing_0 = basis_images[0][0].weil_pairing(basis_images[1][0], C)
    pairing_1 = basis_images[0][1].weil_pairing(basis_images[1][1], C)
    if pairing_0 == source_pairing**B and pairing_1 == source_pairing**A:
        EAC, EBC = EBC, EAC
        basis_images = [
            CouplePoint(image[1], image[0]) for image in basis_images
        ]
    elif pairing_0 != source_pairing**A or pairing_1 != source_pairing**B:
        raise ValueError("Could not identify the EAC and EBC factors.")

    PAC, PBC = basis_images[0]
    QAC, QBC = basis_images[1]

    # Recover the two EABC components of hat(Phi') using
    # e(Phi'(R),S) = e(R,hat(Phi')(S)).
    zeta_ABC = temporary_PABC.weil_pairing(temporary_QABC, C)

    pairing_P = basis_images[2][0].weil_pairing(PAC, C)
    pairing_Q = basis_images[3][0].weil_pairing(PAC, C)
    b = discrete_log(pairing_P, zeta_ABC, ord=C)
    a = -discrete_log(pairing_Q, zeta_ABC, ord=C)
    PABC = a * temporary_PABC + b * temporary_QABC

    pairing_P = basis_images[2][0].weil_pairing(QAC, C)
    pairing_Q = basis_images[3][0].weil_pairing(QAC, C)
    b = discrete_log(pairing_P, zeta_ABC, ord=C)
    a = -discrete_log(pairing_Q, zeta_ABC, ord=C)
    QABC = a * temporary_PABC + b * temporary_QABC

    EAC_kum = KummerLine(EAC)
    EBC_kum = KummerLine(EBC)
    xPC, xQC, xPQC = kummer_basis_from_points(EC_kum, PC, QC)
    xPAC, xQAC, xPQAC = kummer_basis_from_points(EAC_kum, PAC, QAC)
    xPBC, xQBC, xPQBC = kummer_basis_from_points(EBC_kum, PBC, QBC)
    xPABC, xQABC, xPQABC = kummer_basis_from_points(
        EABC_kum, PABC, QABC
    )

    r0123 = randint(0, 2**256 - 1)
    r04 = randint(0, 2**256 - 1)
    r14 = randint(0, 2**256 - 1)
    r24 = randint(0, 2**256 - 1)
    r34 = randint(0, 2**256 - 1)
    r4 = randint(0, 2**256 - 1)

    h0123 = normalize_and_hash(r0123, dual_kernel_vector)
    h04 = normalize_and_hash(r04, EC_kum, xPC, xQC, xPQC)
    h14 = normalize_and_hash(r14, EAC_kum, xPAC, xQAC, xPQAC)
    h24 = normalize_and_hash(r24, EBC_kum, xPBC, xQBC, xPQBC)
    h34 = normalize_and_hash(r34, EABC_kum, xPABC, xQABC, xPQABC)
    h4 = normalize_and_hash(r4, phi_prime_above_kernel)

    # fmt: off
    responses = {
        0: (r0123, dual_kernel_vector, r04, EC_kum, xPC, xQC, xPQC),
        1: (r0123, dual_kernel_vector, r14, EAC_kum, xPAC, xQAC, xPQAC),
        2: (r0123, dual_kernel_vector, r24, EBC_kum, xPBC, xQBC, xPQBC),
        3: (r0123, dual_kernel_vector, r34, EABC_kum, xPABC, xQABC, xPQABC),
        4: (
            r04, EC_kum, xPC, xQC, xPQC,
            r14, EAC_kum, xPAC, xQAC, xPQAC,
            r24, EBC_kum, xPBC, xQBC, xPQBC,
            r34, EABC_kum, xPABC, xQABC, xPQABC,
            r4, phi_prime_above_kernel,
        ),
    }
    # fmt: on
    commitment = (h0123, h04, h14, h24, h34, h4)
    return commitment, responses


def verifier(params, pk, challenge, response, commitment):
    p, N, _, C, _, _, A, B, _, _ = params
    E0, EA, EB, EAB = pk

    if challenge in range(4):
        h0123 = commitment[0]
        h_curve = commitment[challenge + 1]
        r0123, kernel_vector, r_curve, E_kum, xP, xQ, xPQ = response
        if (
            normalize_and_hash(r0123, kernel_vector) != h0123
            or normalize_and_hash(r_curve, E_kum, xP, xQ, xPQ) != h_curve
        ):
            return False
        if not is_supersingular_and_correct_characteristic_kummer(E_kum, p):
            return False
        if not x_only_is_basis_cube(xP, xQ, xPQ, C, E_kum.curve()):
            return False

        target = KummerLine((E0, EA, EB, EAB)[challenge])
        xK = x_only_linear_comb(
            xP, xQ, xPQ, kernel_vector[0], kernel_vector[1], C
        )
        phi = KummerLineIsogeny(E_kum, xK, C)
        if (
            phi.codomain().curve().j_invariant()
            != target.curve().j_invariant()
        ):
            return False

    elif challenge == 4:
        # fmt: off
        (r04, EC_kum, xPC, xQC, xPQC, r14, EAC_kum, xPAC, xQAC, xPQAC, r24, EBC_kum, xPBC, xQBC, xPQBC, r34, EABC_kum, xPABC, xQABC, xPQABC, r4, phi_prime_above_kernel) = response
        # fmt: on
        _, h04, h14, h24, h34, h4 = commitment

        if (
            normalize_and_hash(r04, EC_kum, xPC, xQC, xPQC) != h04
            or normalize_and_hash(r14, EAC_kum, xPAC, xQAC, xPQAC) != h14
            or normalize_and_hash(r24, EBC_kum, xPBC, xQBC, xPQBC) != h24
            or normalize_and_hash(r34, EABC_kum, xPABC, xQABC, xPQABC) != h34
            or normalize_and_hash(r4, phi_prime_above_kernel) != h4
        ):
            return False

        EC = EC_kum.curve()
        EAC = EAC_kum.curve()
        EBC = EBC_kum.curve()
        EABC = EABC_kum.curve()
        if not is_supersingular_and_correct_characteristic_kummer(EC_kum, p):
            return False
        if not x_only_is_basis_cube(xPC, xQC, xPQC, C, EC):
            return False

        lifted_bases = []
        for E_kum, xP, xQ, xPQ in (
            (EC_kum, xPC, xQC, xPQC),
            (EAC_kum, xPAC, xQAC, xPQAC),
            (EBC_kum, xPBC, xQBC, xPQBC),
            (EABC_kum, xPABC, xQABC, xPQABC),
        ):
            P, Q = xP.curve_point(), xQ.curve_point()
            if E_kum(P - Q) != xPQ:
                Q = -Q
            lifted_bases.append((P, Q))
        (PC, QC), (PAC, QAC), (PBC, QBC), (PABC, QABC) = lifted_bases

        # Check that 4*phi_prime_above_kernel generates a non-diagonal,
        # maximal isotropic N-kernel on EC x EABC.
        if len(phi_prime_above_kernel) != 2:
            return False
        if any(
            T.curves() != (EC, EABC) for T in phi_prime_above_kernel
        ):
            return False

        K0 = 4 * phi_prime_above_kernel[0]
        K1 = 4 * phi_prime_above_kernel[1]
        zero = CouplePoint(EC(0), EABC(0))
        if N * K0 != zero or N * K1 != zero:
            return False

        kernel_pairing_0 = K0[0].weil_pairing(K1[0], N)
        kernel_pairing_1 = K0[1].weil_pairing(K1[1], N)
        if (
            kernel_pairing_0 == 1
            or kernel_pairing_1 == 1
            or kernel_pairing_0 * kernel_pairing_1 != 1
            or kernel_pairing_0 ** (N // 2) == 1
        ):
            return False

        # Recompute Phi' on the two opened EC points and on the opened EABC
        # basis. The extra sums resolve the product-Kummer signs.
        zero_C = EC(0)
        zero_ABC = EABC(0)
        product_basis = [
            CouplePoint(PC, zero_ABC),
            CouplePoint(QC, zero_ABC),
            CouplePoint(zero_C, PABC),
            CouplePoint(zero_C, QABC),
        ]
        points_to_evaluate = [
            *product_basis,
            product_basis[0] + product_basis[1],
            product_basis[0] + product_basis[2],
            product_basis[0] + product_basis[3],
        ]

        _, _, _, codomain, images = mapping_E0xE1_to_A_even(
            EC, EABC, phi_prime_above_kernel, N, points_to_evaluate
        )
        splitting_iso = SplittingIsomorphism(codomain)
        split_product = SplitThetaStructure(splitting_iso.codomain())
        images = [split_product(splitting_iso(P)) for P in images]

        basis_images = images[:4]
        sum_images = images[4:]
        corrected_images = [basis_images[0]]
        for image, sum_image in zip(basis_images[1:], sum_images):
            components = [image[0], image[1]]
            for i in range(2):
                if (
                    basis_images[0][i] + components[i] != sum_image[i]
                    and basis_images[0][i] + components[i] != -sum_image[i]
                ):
                    components[i] = -components[i]
            corrected_images.append(CouplePoint(*components))
        basis_images = corrected_images

        computed_EAC, computed_EBC = split_product.curves()
        source_pairing = PC.weil_pairing(QC, C)
        pairing_0 = basis_images[0][0].weil_pairing(basis_images[1][0], C)
        pairing_1 = basis_images[0][1].weil_pairing(basis_images[1][1], C)
        if pairing_0 == source_pairing**B and pairing_1 == source_pairing**A:
            computed_EAC, computed_EBC = computed_EBC, computed_EAC
            basis_images = [
                CouplePoint(image[1], image[0]) for image in basis_images
            ]
        elif pairing_0 != source_pairing**A or pairing_1 != source_pairing**B:
            return False

        if (
            computed_EAC.j_invariant() != EAC.j_invariant()
            or computed_EBC.j_invariant() != EBC.j_invariant()
        ):
            return False

        expected_images = (
            CouplePoint(PAC, PBC),
            CouplePoint(QAC, QBC),
        )
        for computed, expected in zip(basis_images[:2], expected_images):
            for i in range(2):
                if computed[i] != expected[i] and computed[i] != -expected[i]:
                    return False

        # Verify the two asserted EABC components of hat(Phi') using the
        # Weil-pairing adjunction.
        for target, dual_second in ((PAC, PABC), (QAC, QABC)):
            for domain_point, image in zip(product_basis[2:], basis_images[2:]):
                lhs = image[0].weil_pairing(target, C)
                rhs = domain_point[1].weil_pairing(dual_second, C)
                if lhs != rhs and lhs != 1 / rhs:
                    return False

        source_pairing = PC.weil_pairing(QC, C)
        if (
            PAC.weil_pairing(QAC, C) != source_pairing**A
            or PBC.weil_pairing(QBC, C) != source_pairing**B
        ):
            return False

    else:
        return False

    return True


if __name__ == "__main__":
    from kube_params import KUBE_TEST_PARAMS as params

    speed_up_sagemath()
    sk, pk = key_gen(params)
    commitment, response_alg = prover(params, sk, pk)
    for challenge in range(NUM_CHALLENGES):
        assert verifier(
            params, pk, challenge, response_alg[challenge], commitment
        ), f"Verification failed for challenge {challenge}."
    print("Kube-ZKP test passed")
