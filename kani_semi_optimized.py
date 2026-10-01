import time
from itertools import product

from sage.all import Zmod, gcd, matrix, randint

from helpers.helpers import (
    normalize_and_hash,
)
from helpers.montgomery_helpers import (
    is_supersingular_and_correct_characteristic_kummer,
    x_only_push_pair,
)
from helpers.theta_arithmetic import UnsupportedProductError
from helpers.two_dim_utils import (
    get_points_above_kernel,
    has_codomain_and_mapping_two_dim_and_nondiagonal,
    has_codomain_two_dim,
    is_basis_product,
    is_basis_theta,
    is_diagonal_and_has_codomain,
    randomize_basis_two_dim,
    randomize_diagonal_kernel,
)
from vendors.Theta_SageMath.theta_isogenies.product_isogeny import EllipticProductIsogeny
from vendors.Kummer_Isogeny.kummer_isogeny import KummerLineIsogeny
from vendors.Kummer_Isogeny.kummer_line import KummerLine
from vendors.SQIsign2DSquare.rii import RanIso, make_precomputed_values
from vendors.Theta_SageMath.theta_structures.couple_point import CouplePoint
from vendors.Theta_SageMath.utilities.supersingular import (
    compute_linearly_independent_point,
    torsion_basis,
)
from vendors.Theta_SageMath.utilities.utils import speed_up_sagemath


def key_gen(params):
    """Generate the non-smooth Kani diamond using SQISign2DSquare's RanIso construction."""
    p, N, e2, M, e3, c, A, B, _, Fp2 = params

    # This is the full-degree RanIso construction, not ImRanIso.
    global_data = make_precomputed_values(
        p, e2, e3, Fp2, auxiliary_cofactor=c
    )
    ran_iso = RanIso(A, global_data, compute_odd_points=True)

    E0 = ran_iso.E0
    EA = ran_iso.EA
    EB = ran_iso.EB
    EAB = ran_iso.EAB
    K1, K2 = ran_iso.kernel

    above_kernel = get_points_above_kernel(K1, K2, N)
    T1, T2 = above_kernel

    assert p == 4 * N * M * c - 1
    assert A + B == N
    assert gcd(A, B) == 1
    assert ran_iso.alpha.norm() == A * B * M
    assert ran_iso.alpha.content() % 3 != 0
    assert ran_iso.accessible_kernel.order() == M
    assert ran_iso.accessible_isogeny.degree() == M
    assert len(ran_iso.odd_images) == 3
    P3e, Q3e = global_data.E0_data.OddTorsionBases[0]
    odd_points = (
        CouplePoint(P3e, EAB(0)),
        CouplePoint(Q3e, EAB(0)),
        CouplePoint(P3e - Q3e, EAB(0)),
    )
    assert ran_iso.odd_images == tuple(ran_iso.Phi(P) for P in odd_points)

    zero_domain = CouplePoint(E0(0), EAB(0))
    zero_codomain = CouplePoint(EA(0), EB(0))
    assert N * K1 == zero_domain
    assert N * K2 == zero_domain
    assert K1.weil_pairing(K2, N) == 1
    assert K1[1].weil_pairing(K2[1], N) ** (N // 2) != 1
    assert K1[0].weil_pairing(K2[0], N) != 1
    assert 4 * T1 == K1
    assert 4 * T2 == K2
    assert T1[0].weil_pairing(T2[0], 4 * N) ** (2 * N) != 1
    assert T1[1].weil_pairing(T2[1], 4 * N) ** (2 * N) != 1
    assert ran_iso.Phi_raw.n == e2
    assert len(ran_iso.Phi_raw.codomain()) == 2
    assert ran_iso.Phi(K1) == zero_codomain
    assert ran_iso.Phi(K2) == zero_codomain

    # Keep the deliberately bloated witness style. See cube_optimized.py for explanation.
    sk = (ran_iso.kernel, above_kernel, ran_iso.Phi, ran_iso)
    pk = (E0, EA, EB, EAB)
    return sk, pk



# Helper functions for the prover's algorithm.
def prover(params, sk, pk):
    p, N, e2, M, e3, c, A, B, _, Fp2 = params
    _, above_kernel, _, _ = sk
    E0, EA, EB, EAB = pk
    # T1, T2 = above_kernel

    # Construct Psi:E0 x EAB ---> F0 x FAB using x-only Montgomery arithmetic.
    B0, B1, B2, B3 = torsion_basis(E0, M) + torsion_basis(EAB, M)
    Psi_vec = (1, randint(1, M - 1), 1, randint(1, M - 1))
    S0 = B0 + Psi_vec[1] * B1
    S1 = B2 + Psi_vec[3] * B3
    E0_kum = KummerLine(E0)
    EAB_kum = KummerLine(EAB)
    rho_0 = KummerLineIsogeny(E0_kum, E0_kum(S0), M)
    rho_1 = KummerLineIsogeny(EAB_kum, EAB_kum(S1), M)
    F0 = rho_0.codomain().curve()
    FAB = rho_1.codomain().curve()

    # Psi_d kernel is <T0, T3>; the sign of each generator is irrelevant.
    T0 = rho_0(E0_kum(B1)).curve_point()
    T3 = rho_1(EAB_kum(B3)).curve_point()
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

    # Push Phi's kernel through Psi with consistent signs in each component.
    # Either choice of (+-rho_0, +-rho_1) defines a valid Psi.
    T1, T2 = above_kernel
    T1_0, T2_0 = x_only_push_pair(rho_0, T1[0], T2[0])
    T1_1, T2_1 = x_only_push_pair(rho_1, T1[1], T2[1])
    phi_prime_above_kernel = (CouplePoint(T1_0, T1_1), CouplePoint(T2_0, T2_1))
    chain = EllipticProductIsogeny.from_degree(phi_prime_above_kernel, N, split=False)
    J = chain.codomain()
    pushed_basis_with_aux_info = [chain(P) for P in random_basis_with_aux_info]

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


def verifier(params, pk, challenge, response, commitment):
    p, N, e2, M, e3, c, A, B, _, Fp2 = params
    E0, EA, EB, EAB = pk
    if challenge == 0:
        h01, h02, _, _ = commitment
        r01, Xs_in_random_basis, r02, F0, FAB, F0FAB_random_basis = response
        h01_check = normalize_and_hash(r01, Xs_in_random_basis)
        h02_check = normalize_and_hash(r02, F0, FAB, F0FAB_random_basis)
        if h01_check != h01 or h02_check != h02:
            return False

        if not is_supersingular_and_correct_characteristic_kummer(KummerLine(F0), p):
            return False
        if not is_supersingular_and_correct_characteristic_kummer(KummerLine(FAB), p):
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

        if not is_supersingular_and_correct_characteristic_kummer(KummerLine(F0), p):
            return False
        if not is_supersingular_and_correct_characteristic_kummer(KummerLine(FAB), p):
            return False

        if not is_basis_product(F0FAB_random_basis, M, F0, FAB):
            return False

        if not has_codomain_and_mapping_two_dim_and_nondiagonal(
            phi_prime_above_kernel,
            (F0, FAB),
            J,
            N,
            F0FAB_random_basis,
            pushed_basis,
        ):
            return False

    else:
        return False

    return True


def run_trial(trial_num, trials, params):
    while True:
        sk, pk = key_gen(params)
        
        start_prover = time.time()
        commitment, response_alg = prover(params, sk, pk)
        prover_time = time.time() - start_prover
        
        try:
            start_verifier = time.time()
            for challenge in range(3):
                assert verifier(params, pk, challenge, response_alg[challenge], commitment)
            verifier_time = time.time() - start_verifier
            verifier_time /= 3  # Average over the three challenges
            
            return prover_time, verifier_time
        except UnsupportedProductError as exc:
            print(
                f"Trial {trial_num + 1}: product signs unavailable ({exc}). Retrying.",
                flush=True,
            )


if __name__ == "__main__":
    import time
    from multiprocessing import Pool
    speed_up_sagemath()
    from kani_params import KANI_128_PARAMS_HEUR as params

    trials = 16
    num_reps = params[8]
    
    with Pool(processes=trials) as pool:
        results = pool.starmap(run_trial, [(i, trials, params) for i in range(trials)])
    
    prover_times = [r[0] for r in results]
    verifier_times = [r[1] for r in results]
    
    avg_prover = sum(prover_times) / len(prover_times)
    avg_verifier = sum(verifier_times) / len(verifier_times)
    print(f"Average prover time: {avg_prover:.2f} seconds")
    print(f"Average verifier time: {avg_verifier:.2f} seconds")
    print(f"Prover time (after {num_reps} reps): {avg_prover * num_reps:.2f} seconds")
    print(f"Verifier time (after {num_reps} reps): {avg_verifier * num_reps:.2f} seconds")