from itertools import product

from sage.all import (
    GF,
    EllipticCurve,
    Zmod,
    matrix,
    randint,
)

from helpers.ec_utils import (
    is_supersingular_and_correct_characteristic,
    random_supersingular_curve,
)
from helpers.helpers import (
    normalize_and_hash,
)
from helpers.two_dim_utils import (
    has_codomain_and_mapping_two_dim_and_nondiagonal,
    has_codomain_two_dim,
    is_basis_product,
    is_basis_theta,
    is_diagonal_and_has_codomain,
    randomize_basis_two_dim,
    randomize_diagonal_kernel,
)
from helpers.two_dim_wrappers import (
    mapping_E0xE1_to_A_even,
)
from vendors.Theta_SageMath.theta_structures.couple_point import CouplePoint
from vendors.Theta_SageMath.utilities.supersingular import (
    compute_linearly_independent_point,
    torsion_basis,
)

# Sample parameters for proof of concept.
e2 = 11
e3 = 8
N = 2**e2
M = 3**e3
a = 29 * 53
b = 7 * 73
p = 4 * N * M * a * b - 1

Fp2 = GF(p**2, modulus=[1, 0, 1], names="i")
E_j0 = EllipticCurve(Fp2, [0, 1]).montgomery_model()


# Need additional torsion above the kernel to compute the (2^e2, 2^e2)isogeny.
def get_points_above_kernel(K1, K2):
    """Find points T1, T2 such that 4T1 = K1, 4T2 = K2, and the Weil pairing of T1 and T2
    descends down to pairing on the kernel."""
    T1_0_cands = K1[0].division_points(4)
    T1_1_cands = K1[1].division_points(4)
    T2_0_cands = K2[0].division_points(4)
    T2_1_cands = K2[1].division_points(4)

    zeta = K1[0].weil_pairing(K2[0], N * 4)

    for (t1_0, t1_1), (t2_0, t2_1) in product(
        product(T1_0_cands, T1_1_cands), product(T2_0_cands, T2_1_cands)
    ):
        if (
            t1_0.weil_pairing(t2_0, N * 4) ** 16 == zeta
            and t1_1.weil_pairing(t2_1, N * 4) ** 16 == 1 / zeta
        ):
            T1 = CouplePoint(t1_0, t1_1)
            T2 = CouplePoint(t2_0, t2_1)
            return (T1, T2)
    raise ValueError("No points above kernel found")


##### Construct the Kani Diamond (Statement to prove) #####
def one_dim_key_gen():
    E0 = random_supersingular_curve(p)
    a_torsion_basis = E0.torsion_basis(a)
    b_torsion_basis = E0.torsion_basis(b)

    # Generate an isogeny diamond.
    sk = (randint(0, a - 1), randint(0, b - 1))
    S_A = a_torsion_basis[0] + sk[0] * a_torsion_basis[1]
    S_B = b_torsion_basis[0] + sk[1] * b_torsion_basis[1]
    phi_A = E0.isogeny(S_A, algorithm="factored", model="montgomery")
    phi_B = E0.isogeny(S_B, algorithm="factored", model="montgomery")
    EA = phi_A.codomain()
    EB = phi_B.codomain()
    S_AB = phi_A(S_B)
    S_BA = phi_B(S_A)
    psi_AB = EA.isogeny(S_AB, algorithm="factored", model="montgomery")
    EAB = psi_AB.codomain()
    psi_BA = EB.isogeny(S_BA, algorithm="factored", codomain=EAB)

    # Correct dual sign inconsistency if necessary.
    P = E0.random_point()
    if psi_AB(phi_A(P)) != psi_BA(phi_B(P)):
        psi_BA = -psi_BA

    N_torsion_basis = E0.torsion_basis(N)
    K1 = CouplePoint(a * N_torsion_basis[0], psi_AB(phi_A(N_torsion_basis[0])))
    K2 = CouplePoint(a * N_torsion_basis[1], psi_AB(phi_A(N_torsion_basis[1])))

    kernel = (K1, K2)

    above_kernel = get_points_above_kernel(K1, K2)
    T1, T2 = above_kernel

    # Reality Check: above_kernel generates all 4N-torsion
    assert T1[0].weil_pairing(T2[0], N * 4).multiplicative_order() == N * 4
    assert T1[1].weil_pairing(T2[1], N * 4).multiplicative_order() == N * 4
    assert 4 * T1 == K1 and 4 * T2 == K2

    psi_AB_d = psi_AB.dual()
    psi_BA_d = psi_BA.dual()

    def Phi(domain_pt: CouplePoint):
        X, Y = domain_pt[0], domain_pt[1]
        return CouplePoint(phi_A(X) + psi_AB_d(Y), phi_B(X) - psi_BA_d(Y))

    sk = (kernel, above_kernel, Phi)
    pk = (E0, EA, EB, EAB)
    return sk, pk


# Helper functions for the prover's algorithm.
def prover(sk, pk):
    kernel, above_kernel, Phi = sk
    E0, EA, EB, EAB = pk
    # K1, K2 = kernel
    # T1, T2 = above_kernel

    # Construct diagonal isogeny: Psi:E0 x EAB ---> F0 x FAB
    B0, B1, B2, B3 = torsion_basis(E0, M) + torsion_basis(EAB, M)
    Psi_vec = (1, randint(1, M - 1), 1, randint(1, M - 1))
    S0 = B0 + Psi_vec[1] * B1
    S1 = B2 + Psi_vec[3] * B3
    rho_0 = E0.isogeny(S0, algorithm="factored", model="montgomery")
    rho_1 = EAB.isogeny(S1, algorithm="factored", model="montgomery")
    F0 = rho_0.codomain()
    FAB = rho_1.codomain()

    def Psi(R: CouplePoint) -> CouplePoint:
        return CouplePoint(rho_0(R[0]), rho_1(R[1]))

    # Psi_d kernel is <T0, T3>
    T0, T3 = rho_0(B1), rho_1(B3)
    # Pick random independent point
    T0_indep = compute_linearly_independent_point(F0, T0, M, x_start=randint(0, p - 1))
    T3_indep = compute_linearly_independent_point(FAB, T3, M, x_start=randint(0, p - 1))
    _, _, diag_change_basis = randomize_diagonal_kernel(T0, T3, M)
    F0FAB_basis = [
        CouplePoint(T0, FAB(0)),
        CouplePoint(T0_indep, FAB(0)),
        CouplePoint(F0(0), T3),
        CouplePoint(F0(0), T3_indep),
    ]
    # with respect to F0FAB_basis
    Xs_in_Ts = matrix(
        Zmod(M),
        [
            [diag_change_basis[0, 0], 0, diag_change_basis[0, 1], 0],
            [diag_change_basis[1, 0], 0, diag_change_basis[1, 1], 0],
        ],
    )
    F0FAB_random_basis, _, Xs_in_random_basis = randomize_basis_two_dim(
        F0FAB_basis, M, kernel_matrix=Xs_in_Ts
    )

    # For technical reasons due to sign ambiguities, we need to provide the verifier with some differences of the basis points on the theta structure.
    # In particular, we need B0 - B2, B0 - B3, B1 - B2, and B1 - B3. See theta_matrix_basis_to_pts in ec_helpers.py for more info.
    random_basis_with_aux_info = [
        *F0FAB_random_basis,
        F0FAB_random_basis[0] + F0FAB_random_basis[1],
        F0FAB_random_basis[0] + F0FAB_random_basis[2],
        F0FAB_random_basis[0] + F0FAB_random_basis[3],
        F0FAB_random_basis[1] + F0FAB_random_basis[2],
        F0FAB_random_basis[1] + F0FAB_random_basis[3],
        F0FAB_random_basis[2] + F0FAB_random_basis[3],
    ]

    # Compute Phi'. the pused isogeny, on the random basis.
    phi_prime_above_kernel = (Psi(above_kernel[0]), Psi(above_kernel[1]))
    _, _, _, J, pushed_basis_with_aux_info = mapping_E0xE1_to_A_even(
        F0, FAB, phi_prime_above_kernel, N, random_basis_with_aux_info, M
    )

    # Now we hash various public data to make the commitments.
    r01 = randint(0, 2**256 - 1)
    r02 = randint(0, 2**256 - 1)
    r12 = randint(0, 2**256 - 1)
    r2 = randint(0, 2**256 - 1)

    h01 = normalize_and_hash(r01, Xs_in_random_basis)
    h02 = normalize_and_hash(r02, F0, FAB, F0FAB_random_basis)
    h12 = normalize_and_hash(r12, J, pushed_basis_with_aux_info)
    h2 = normalize_and_hash(r2, phi_prime_above_kernel)

    # fmt: off
    responses = {
        0: (r01, Xs_in_random_basis, r02, F0, FAB, F0FAB_random_basis),
        1: (r01, Xs_in_random_basis, r12, J, pushed_basis_with_aux_info),
        2: (r02, F0, FAB, F0FAB_random_basis, r12, J, pushed_basis_with_aux_info, r2, phi_prime_above_kernel),
    }
    # fmt: on
    commitment = (h01, h02, h12, h2)
    return commitment, responses


def verifier(pk, challenge, response, commitment):
    E0, EA, EB, EAB = pk
    if challenge == 0:
        h01, h02, _, _ = commitment
        r01, Xs_in_random_basis, r02, F0, FAB, F0FAB_random_basis = response
        h01_check = normalize_and_hash(r01, Xs_in_random_basis)
        h02_check = normalize_and_hash(r02, F0, FAB, F0FAB_random_basis)
        if h01_check != h01 or h02_check != h02:
            return False

        if not is_supersingular_and_correct_characteristic(
            F0, p
        ) or not is_supersingular_and_correct_characteristic(FAB, p):
            return False

        if not is_basis_product(F0FAB_random_basis, M, F0, FAB):
            return False

        if not is_diagonal_and_has_codomain(
            Xs_in_random_basis,
            F0FAB_random_basis,
            M,
            (F0, FAB),
            (E0, EAB),
        ):
            return False

    elif challenge == 1:
        h01, _, h12, _ = commitment
        r01, Xs_in_random_basis, r12, J, pushed_basis_with_aux_info = response
        h01_check = normalize_and_hash(r01, Xs_in_random_basis)
        h12_check = normalize_and_hash(r12, J, pushed_basis_with_aux_info)
        if h01_check != h01 or h12_check != h12:
            return False

        pushed_basis = pushed_basis_with_aux_info[:4]
        aux_info = pushed_basis_with_aux_info[4:]

        if not is_basis_theta(pushed_basis, M, J):
            return False

        if not has_codomain_two_dim(Xs_in_random_basis, pushed_basis, aux_info, M, J, (EA, EB)):
            return False

    elif challenge == 2:
        _, h02, h12, h2 = commitment
        (
            r02,
            F0,
            FAB,
            F0FAB_random_basis,
            r12,
            J,
            pushed_basis_with_aux_info,
            r2,
            phi_prime_above_kernel,
        ) = response
        h02_check = normalize_and_hash(r02, F0, FAB, F0FAB_random_basis)
        h12_check = normalize_and_hash(r12, J, pushed_basis_with_aux_info)
        h2_check = normalize_and_hash(r2, phi_prime_above_kernel)
        if h02_check != h02 or h12_check != h12 or h2_check != h2:
            return False

        pushed_basis = pushed_basis_with_aux_info[:4]
        aux_info = pushed_basis_with_aux_info[4:]

        if not is_supersingular_and_correct_characteristic(
            F0, p
        ) or not is_supersingular_and_correct_characteristic(FAB, p):
            return False

        if not is_basis_product(F0FAB_random_basis, M, F0, FAB):
            return False

        if not has_codomain_and_mapping_two_dim_and_nondiagonal(
            phi_prime_above_kernel, (F0, FAB), J, N, F0FAB_random_basis, pushed_basis
        ):
            return False

    return True


if __name__ == "__main__":
    while True:
        sk, pk = one_dim_key_gen()
        commitment, response_alg = prover(sk, pk)
        try:
            for challenge in range(3):
                assert verifier(pk, challenge, response_alg[challenge], commitment)
            break
        except ValueError:
            print("Odd isogeny contains an intermediate product. Trying again.")
