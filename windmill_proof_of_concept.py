from sage.all import (
    GF,
    EllipticCurve,
    gcd,
    inverse_mod,
    randint,
)

from helpers.ec_utils import (
    get_coefficients_wrt,
    has_codomain,
    has_codomain_and_mapping,
    is_basis_windmill,
    is_supersingular_and_correct_characteristic,
    randomize_basis,
)
from helpers.helpers import (
    normalize_and_hash,
)

A = 2**2 * 3 * 7 * 13 * 19 * 29
B = 5 * 11 * 17 * 23
f = 3
p = A * B * f - 1
num_reps = 1
A_ells = [2, 7, 13, 19, 29]
B_ells = [5, 11, 17, 23]

Fp2 = GF(p**2, modulus=[1, 0, 1], names="i")
E0 = EllipticCurve(Fp2, [0, 1])

a_torsion_basis = E0.torsion_basis(A)
b_torsion_basis = E0.torsion_basis(B)

params = (p, A, B, num_reps, Fp2, E0, a_torsion_basis, b_torsion_basis)


def key_gen(params):
    p, A, B, num_reps, Fp2, E0, a_torsion_basis, b_torsion_basis = params
    """Constructs the secret Isogeny Diamond (Statement to prove)"""
    sk_ints = (randint(1, A - 1), randint(1, B - 1))
    S_A = a_torsion_basis[0] + sk_ints[0] * a_torsion_basis[1]
    S_B = b_torsion_basis[0] + sk_ints[1] * b_torsion_basis[1]
    phi_A = E0.isogeny(S_A, algorithm="factored")
    phi_B = E0.isogeny(S_B, algorithm="factored")
    EA = phi_A.codomain()
    EB = phi_B.codomain()
    S_AB = phi_A(S_B)
    S_BA = phi_B(S_A)
    psi_AB = EA.isogeny(S_AB, algorithm="factored")
    psi_BA = EB.isogeny(S_BA, algorithm="factored")
    EAB = psi_BA.codomain()
    # If any of the codomain assertions fail, need to add correcting isomorphism.
    assert EAB == psi_AB.codomain(), f"Isomorphic? {EAB.isomorphic_to(psi_AB.codomain())}."

    # Generate random masking scalars 
    alpha = randint(1, B - 1)
    while gcd(alpha, B) != 1:
        alpha = randint(1, B - 1)

    xi = randint(1, A - 1)
    while gcd(xi, A) != 1:
        xi = randint(1, A - 1)

    masked_torsion = [
        alpha * phi_A(b_torsion_basis[0]),
        alpha * phi_A(b_torsion_basis[1]),
        xi * phi_B(a_torsion_basis[0]),
        xi * phi_B(a_torsion_basis[1]),
    ]

    # Secret key: we return everything for now.
    sk = (phi_A, phi_B, psi_AB, psi_BA, S_A, S_B, S_AB, S_BA, sk_ints, alpha, xi)
    pk = (E0, EA, EB, EAB, masked_torsion)
    return sk, pk


def get_independent_point(torsion_basis, pt, N, ells):
    "Given a basis for E[N] where N = prod(ells), returns a random point that is independent from pt."
    indep_point = torsion_basis[0] + torsion_basis[1] * randint(1, N - 1)
    while any(indep_point.weil_pairing(pt, N) ** (N // ell_i) == 1 for ell_i in ells):
        indep_point = torsion_basis[0] + torsion_basis[1] * randint(1, N - 1)

    return indep_point


"""Notice how in the windmill, the prover does not need to know sk_B."""
def prover(params, sk, pk):
    p, A, B, num_reps, Fp2, E0, a_torsion_basis, b_torsion_basis = params
    _, _, _, _, S_A, _, _, _, (sk_A, _), alpha, _ = sk
    E0, EA, EB, EAB, masked_torsion = pk

    # Sample random basis of b-torsion.
    B_random_basis, _ = randomize_basis(b_torsion_basis, B)

    K_psi_L0, K_psi_L1 = B_random_basis
    psi_L0 = E0.isogeny(K_psi_L0, algorithm="factored")
    psi_L1 = E0.isogeny(K_psi_L1, algorithm="factored")
    EL0 = psi_L0.codomain()
    EL1 = psi_L1.codomain()

    (K_psi_L2, K_psi_L2_indep), _ = randomize_basis(EB.torsion_basis(B), B)
    psi_L2 = EB.isogeny(K_psi_L2, algorithm="factored")
    EL2 = psi_L2.codomain()

    K_phi_0 = psi_L0(S_A)
    K_phi_1 = psi_L1(S_A)
    phi_0 = EL0.isogeny(K_phi_0, algorithm="factored")
    phi_1 = EL1.isogeny(K_phi_1, algorithm="factored")

    K_phi_2 = psi_L2(masked_torsion[2] + sk_A * masked_torsion[3])
    phi_2 = EL2.isogeny(K_phi_2, algorithm="factored")

    beta = randint(1, B - 1)
    while gcd(beta, B) != 1:
        beta = randint(1, B - 1)

    ER0 = phi_0.codomain()
    ER1 = phi_1.codomain()
    ER2 = phi_2.codomain()

    K_psi_L0_d = psi_L0(K_psi_L1)
    K_psi_L1_d = psi_L1(K_psi_L0)
    psi_L0_d = EL0.isogeny(K_psi_L0_d, algorithm="factored", codomain=E0)
    psi_L1_d = EL1.isogeny(K_psi_L1_d, algorithm="factored", codomain=E0)

    K_psi_L2_d = psi_L2(K_psi_L2_indep)

    K_psi_L0_indep = get_independent_point(EL0.torsion_basis(B), K_psi_L0_d, B, B_ells)
    K_psi_L1_indep = get_independent_point(EL1.torsion_basis(B), K_psi_L1_d, B, B_ells)
    K_psi_L2_indep = get_independent_point(EL2.torsion_basis(B), K_psi_L2_d, B, B_ells)
    EL0_special_basis = [K_psi_L0_d, K_psi_L0_indep]
    EL1_special_basis = [K_psi_L1_d, K_psi_L1_indep]
    EL2_special_basis = [K_psi_L2_d, K_psi_L2_indep]

    EL0_random_basis, EL0_change_of_basis = randomize_basis(EL0_special_basis, B)
    EL1_random_basis, EL1_change_of_basis = randomize_basis(EL1_special_basis, B)
    EL2_random_basis, EL2_change_of_basis = randomize_basis(EL2_special_basis, B)
    PL0, QL0 = EL0_random_basis
    PL1, QL1 = EL1_random_basis
    PL2, QL2 = EL2_random_basis

    K_psi_L0_d_in_PQ, K_psi_L0_indep_in_PQ = EL0_change_of_basis.inverse().rows()
    K_psi_L1_d_in_PQ, K_psi_L1_indep_in_PQ = EL1_change_of_basis.inverse().rows()
    K_psi_L2_d_in_PQ, _ = EL2_change_of_basis.inverse().rows()

    ER0_random_basis = [beta * phi_0(PL0), beta * phi_0(QL0)]
    ER1_random_basis = [beta * phi_1(PL1), beta * phi_1(QL1)]
    ER2_random_basis = [beta * phi_2(PL2), beta * phi_2(QL2)]
    PR0, QR0 = ER0_random_basis
    PR1, QR1 = ER1_random_basis
    PR2, QR2 = ER2_random_basis

    A_random_basis, A_change_of_basis, K_phi_A_in_random_basis = randomize_basis(
        a_torsion_basis, A, [1, sk_A]
    )

    U, V = A_random_basis
    rho_B_on_U = (
        A_change_of_basis[0, 0] * masked_torsion[2] + A_change_of_basis[0, 1] * masked_torsion[3]
    )
    rho_B_on_V = (
        A_change_of_basis[1, 0] * masked_torsion[2] + A_change_of_basis[1, 1] * masked_torsion[3]
    )

    gamma = inverse_mod(alpha, B) * beta

    U0, V0 = psi_L0(U), psi_L0(V)
    U1, V1 = psi_L1(U), psi_L1(V)
    U2, V2 = psi_L2(rho_B_on_U), psi_L2(rho_B_on_V)

    R0 = psi_L0_d(K_psi_L0_indep) # B * K_psi_L0_indep = a * psi_L0(b_torsion[0]) + b * psi_L0(b_torsion[1])
    R1 = psi_L1_d(K_psi_L1_indep)

    R0_in_b_torsion = get_coefficients_wrt(b_torsion_basis[0], b_torsion_basis[1], R0, B)
    R1_in_b_torsion = get_coefficients_wrt(b_torsion_basis[0], b_torsion_basis[1], R1, B)

    scalars = (
        K_psi_L0_d_in_PQ,
        K_psi_L1_d_in_PQ,
        K_psi_L2_d_in_PQ,
        K_psi_L0_indep_in_PQ,
        K_psi_L1_indep_in_PQ,
        R0_in_b_torsion,
        R1_in_b_torsion,
    )

    # # Now we hash various public data to make the commitments.
    r3 = randint(0, 2**256 - 1)
    r4 = randint(0, 2**256 - 1)
    r30 = randint(0, 2**256 - 1)
    r31 = randint(0, 2**256 - 1)
    r32 = randint(0, 2**256 - 1)
    r34 = randint(0, 2**256 - 1)
    r40 = randint(0, 2**256 - 1)
    r41 = randint(0, 2**256 - 1)
    r42 = randint(0, 2**256 - 1)
    r012 = randint(0, 2**256 - 1)  # 10 nonces

    h3 = normalize_and_hash(r3, U, V)
    h4 = normalize_and_hash(r4, gamma)
    h30 = normalize_and_hash(r30, EL0, U0, V0, PL0, QL0)
    h31 = normalize_and_hash(r31, EL1, U1, V1, PL1, QL1)
    h32 = normalize_and_hash(r32, EL2, U2, V2, PL2, QL2)
    h34 = normalize_and_hash(r34, *scalars)
    h40 = normalize_and_hash(r40, ER0, PR0, QR0)
    h41 = normalize_and_hash(r41, ER1, PR1, QR1)
    h42 = normalize_and_hash(r42, ER2, PR2, QR2)
    h012 = normalize_and_hash(r012, K_phi_A_in_random_basis, beta)

    # fmt: off
    responses = {
        0: (r30, EL0, U0, V0, PL0, QL0, r40, ER0, PR0, QR0, r012, K_phi_A_in_random_basis, beta),
        1: (r31, EL1, U1, V1, PL1, QL1, r41, ER1, PR1, QR1, r012, K_phi_A_in_random_basis, beta),
        2: (r32, EL2, U2, V2, PL2, QL2, r42, ER2, PR2, QR2, r012, K_phi_A_in_random_basis, beta),
        3: (r3, U, V, r30, EL0, U0, V0, PL0, QL0, r31, EL1, U1, V1, PL1, QL1, r32, EL2, U2, V2, PL2, QL2, r34, *scalars),
        4: (r4, gamma, r34, *scalars, r40, ER0, PR0, QR0, r41, ER1, PR1, QR1, r42, ER2, PR2, QR2),
    }
    # fmt: on
    commitment = (h3, h4, h30, h31, h32, h34, h40, h41, h42, h012)

    return commitment, responses


def verifier(params, pk, challenge, response, commitment):
    p, A, B, num_reps, Fp2, E0, a_torsion_basis, b_torsion_basis = params
    E0, EA, EB, EAB, masked_torsion = pk
    if challenge == 0:
        h30 = commitment[2]
        h40 = commitment[6]
        h012 = commitment[9]
        r30, EL0, U0, V0, PL0, QL0, r40, ER0, PR0, QR0, r012, K_phi_A_in_random_basis, beta = (
            response
        )
        h30_check = normalize_and_hash(r30, EL0, U0, V0, PL0, QL0)
        h40_check = normalize_and_hash(r40, ER0, PR0, QR0)
        h012_check = normalize_and_hash(r012, K_phi_A_in_random_basis, beta)
        if h30 != h30_check or h40 != h40_check or h012 != h012_check:
            return False

        if not is_supersingular_and_correct_characteristic(EL0, p):
            return False
        if not is_supersingular_and_correct_characteristic(ER0, p):
            return False
        if not is_basis_windmill(U0, V0, A, A_ells, EL0):
            return False
        if not is_basis_windmill(PL0, QL0, B, B_ells, EL0):
            return False
        if not has_codomain_and_mapping(
            K_phi_A_in_random_basis, [U0, V0], A, EL0, ER0, [beta * PL0, beta * QL0], [PR0, QR0]
        ):
            return False
    elif challenge == 1:
        h31 = commitment[3]
        h41 = commitment[7]
        h012 = commitment[9]
        r31, EL1, U1, V1, PL1, QL1, r41, ER1, PR1, QR1, r012, K_phi_A_in_random_basis, beta = (
            response
        )
        h31_check = normalize_and_hash(r31, EL1, U1, V1, PL1, QL1)
        h41_check = normalize_and_hash(r41, ER1, PR1, QR1)
        h012_check = normalize_and_hash(r012, K_phi_A_in_random_basis, beta)
        if h31 != h31_check or h41 != h41_check or h012 != h012_check:
            return False

        if not is_supersingular_and_correct_characteristic(EL1, p):
            return False
        if not is_supersingular_and_correct_characteristic(ER1, p):
            return False
        if not is_basis_windmill(U1, V1, A, A_ells, EL1):
            return False
        if not is_basis_windmill(PL1, QL1, B, B_ells, EL1):
            return False
        if not has_codomain_and_mapping(
            K_phi_A_in_random_basis, [U1, V1], A, EL1, ER1, [beta * PL1, beta * QL1], [PR1, QR1]
        ):
            return False
    elif challenge == 2:
        h32 = commitment[4]
        h42 = commitment[8]
        h012 = commitment[9]
        r32, EL2, U2, V2, PL2, QL2, r42, ER2, PR2, QR2, r012, K_phi_A_in_random_basis, beta = (
            response
        )
        h32_check = normalize_and_hash(r32, EL2, U2, V2, PL2, QL2)
        h42_check = normalize_and_hash(r42, ER2, PR2, QR2)
        h012_check = normalize_and_hash(r012, K_phi_A_in_random_basis, beta)
        if h32 != h32_check or h42 != h42_check or h012 != h012_check:
            return False

        if not is_supersingular_and_correct_characteristic(EL2, p):
            return False
        if not is_supersingular_and_correct_characteristic(ER2, p):
            return False
        if not is_basis_windmill(U2, V2, A, A_ells, EL2):
            return False
        if not is_basis_windmill(PL2, QL2, B, B_ells, EL2):
            return False
        if not has_codomain_and_mapping(
            K_phi_A_in_random_basis,
            [U2, V2],
            A,
            EL2,
            ER2,
            [beta * PL2, beta * QL2],
            [PR2, QR2],
        ):
            return False

    elif challenge == 3:
        h3 = commitment[0]
        h30 = commitment[2]
        h31 = commitment[3]
        h32 = commitment[4]
        h34 = commitment[5]
        #fmt: off
        r3, U, V, r30, EL0, U0, V0, PL0, QL0, r31, EL1, U1, V1, PL1, QL1, r32, EL2, U2, V2, PL2, QL2, r34, *scalars = response
        # fmt: on
        h3_check = normalize_and_hash(r3, U, V)
        h30_check = normalize_and_hash(r30, EL0, U0, V0, PL0, QL0)
        h31_check = normalize_and_hash(r31, EL1, U1, V1, PL1, QL1)
        h32_check = normalize_and_hash(r32, EL2, U2, V2, PL2, QL2)
        h34_check = normalize_and_hash(r34, *scalars)
        if (
            h3 != h3_check
            or h30 != h30_check
            or h31 != h31_check
            or h32 != h32_check
            or h34 != h34_check
        ):
            return False

        (
            K_psi_L0_d_in_PQ,
            K_psi_L1_d_in_PQ,
            K_psi_L2_d_in_PQ,
            K_psi_L0_indep_in_PQ,
            K_psi_L1_indep_in_PQ,
            R0_in_b_torsion,
            R1_in_b_torsion,
        ) = scalars
        R0 = R0_in_b_torsion[0] * b_torsion_basis[0] + R0_in_b_torsion[1] * b_torsion_basis[1]
        R1 = R1_in_b_torsion[0] * b_torsion_basis[0] + R1_in_b_torsion[1] * b_torsion_basis[1]

        if not is_supersingular_and_correct_characteristic(EL0, p):
            return False
        if not is_supersingular_and_correct_characteristic(EL1, p):
            return False
        if not is_supersingular_and_correct_characteristic(EL2, p):
            return False

        if not is_basis_windmill(U, V, A, A_ells, E0):
            return False
        if not is_basis_windmill(PL0, QL0, B, B_ells, EL0):
            return False
        if not is_basis_windmill(PL1, QL1, B, B_ells, EL1):
            return False
        if not is_basis_windmill(PL2, QL2, B, B_ells, EL2):
            return False
        if not is_basis_windmill(R0, R1, B, B_ells, E0):
            return False

        K_psi_L0_indep = K_psi_L0_indep_in_PQ[0] * PL0 + K_psi_L0_indep_in_PQ[1] * QL0
        K_psi_L1_indep = K_psi_L1_indep_in_PQ[0] * PL1 + K_psi_L1_indep_in_PQ[1] * QL1
        if not has_codomain_and_mapping(
            K_psi_L0_d_in_PQ,
            [PL0, QL0],
            B,
            EL0,
            E0,
            [U0, V0, K_psi_L0_indep],
            [B * U, B * V, R0],
        ):
            return False
        if not has_codomain_and_mapping(
            K_psi_L1_d_in_PQ,
            [PL1, QL1],
            B,
            EL1,
            E0,
            [U1, V1, K_psi_L1_indep],
            [B * U, B * V, R1],
        ):
            return False

        U_in_a_torsion = get_coefficients_wrt(a_torsion_basis[0], a_torsion_basis[1], U, A)
        V_in_a_torsion = get_coefficients_wrt(a_torsion_basis[0], a_torsion_basis[1], V, A)
        rho_B_on_U = U_in_a_torsion[0] * masked_torsion[2] + U_in_a_torsion[1] * masked_torsion[3]
        rho_B_on_V = V_in_a_torsion[0] * masked_torsion[2] + V_in_a_torsion[1] * masked_torsion[3]
    
        if not has_codomain_and_mapping(
            K_psi_L2_d_in_PQ,
            [PL2, QL2],
            B,
            EL2,
            EB,
            [U2, V2],
            [B * rho_B_on_U, B * rho_B_on_V],
        ):
            return False

    elif challenge == 4:
        h4 = commitment[1]
        h34 = commitment[5]
        h40 = commitment[6]
        h41 = commitment[7]
        h42 = commitment[8]
        r4, gamma, r34, *scalars, r40, ER0, PR0, QR0, r41, ER1, PR1, QR1, r42, ER2, PR2, QR2 = (
            response
        )
        h4_check = normalize_and_hash(r4, gamma)
        h34_check = normalize_and_hash(r34, *scalars)
        h40_check = normalize_and_hash(r40, ER0, PR0, QR0)
        h41_check = normalize_and_hash(r41, ER1, PR1, QR1)
        h42_check = normalize_and_hash(r42, ER2, PR2, QR2)
        if (
            h4 != h4_check
            or h34 != h34_check
            or h40 != h40_check
            or h41 != h41_check
            or h42 != h42_check
        ):
            return False
        (
            K_psi_L0_d_in_PQ,
            K_psi_L1_d_in_PQ,
            K_psi_L2_d_in_PQ,
            K_psi_L0_indep_in_PQ,
            K_psi_L1_indep_in_PQ,
            R0_in_b_torsion,
            R1_in_b_torsion,
        ) = scalars

        R0_prime = R0_in_b_torsion[0] * masked_torsion[0] + R0_in_b_torsion[1] * masked_torsion[1]
        R1_prime = R1_in_b_torsion[0] * masked_torsion[0] + R1_in_b_torsion[1] * masked_torsion[1]

        if not is_supersingular_and_correct_characteristic(ER0, p):
            return False
        if not is_supersingular_and_correct_characteristic(ER1, p):
            return False
        if not is_supersingular_and_correct_characteristic(ER2, p):
            return False
        if not is_basis_windmill(PR0, QR0, B, B_ells, ER0):
            return False
        if not is_basis_windmill(PR1, QR1, B, B_ells, ER1):
            return False
        if not is_basis_windmill(PR2, QR2, B, B_ells, ER2):
            return False
        if not is_basis_windmill(R0_prime, R1_prime, B, B_ells, EA):
            return False

        K_psi_R0_indep = K_psi_L0_indep_in_PQ[0] * PR0 + K_psi_L0_indep_in_PQ[1] * QR0
        K_psi_R1_indep = K_psi_L1_indep_in_PQ[0] * PR1 + K_psi_L1_indep_in_PQ[1] * QR1
        if not has_codomain_and_mapping(
            K_psi_L0_d_in_PQ,
            [PR0, QR0],
            B,
            ER0,
            EA,
            [K_psi_R0_indep],
            [gamma * R0_prime],
        ):
            return False

        if not has_codomain_and_mapping(
            K_psi_L1_d_in_PQ,
            [PR1, QR1],
            B,
            ER1,
            EA,
            [K_psi_R1_indep],
            [gamma * R1_prime],
        ):
            return False

        if not has_codomain(
            K_psi_L2_d_in_PQ,
            [PR2, QR2],
            B,
            ER2,
            EAB,
        ):
            return False

    return True


if __name__ == "__main__":
    sk, pk = key_gen(params)
    commitment, response_alg = prover(params, sk, pk)
    for challenge in range(5):
        assert verifier(params, pk, challenge, response_alg[challenge], commitment), f"Verification failed for challenge {challenge}."
