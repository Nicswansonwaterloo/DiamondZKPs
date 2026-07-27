import hashlib
import time

from sage.all import Zmod, randint, vector

from helpers.ec_utils import find_independent_point, random_supersingular_curve
from helpers.helpers import normalize_and_hash
from helpers.montgomery_helpers import (
    is_supersingular_and_correct_characteristic_kummer,
    kummer_basis_from_points,
    random_kummer_basis,
    x_only_has_codomain,
    x_only_has_codomain_and_mapping,
    x_only_has_codomain_and_mapping_given_kernel,
    x_only_is_basis_cube,
)
from vendors.Kummer_Isogeny.kummer_isogeny import KummerLineIsogeny
from vendors.Kummer_Isogeny.kummer_line import KummerLine
from vendors.Theta_SageMath.utilities.supersingular import (
    fix_torsion_basis_renes,
    torsion_basis,
)

NUM_CHALLENGES = 7

"""
    When using montgomery curves/Kummer lines, we speed up isogeny computations by about 5-10times by keeping track only of the x-coordinates of our points. This is where the prefix x comes from in the code below. Moreover, every time we need to specify a torsion basis sufficient for performing abitrary additions within that basis, we need to additionally communicate the image of P + Q in the Kummer line, which is what we call xPQ. Helpers for various operations can be found in the helpers/montgomery_helpers.py file.
"""


def key_gen(params):
    """Constructs a random isogeny diamond."""
    p, A, ea, B, _, C, *_ = params

    # Pick a random montgomery E0 and fix torsion bases for E0.
    # Also put objects into Kummer form for faster isogeny computations. This typically requires carrying around P + Q.
    E0 = random_supersingular_curve(p)
    E0_kum = KummerLine(E0)
    # Make sure that (0, 0) is never the kernel at the end of (2, 2) isogeny walk.
    a_torsion_basis = torsion_basis(E0, A)
    a_torsion_basis = fix_torsion_basis_renes(*a_torsion_basis, ea)
    b_torsion_basis = torsion_basis(E0, B)
    c_torsion_basis = torsion_basis(E0, C)

    xPa, xQa, xPQa = kummer_basis_from_points(E0_kum, *a_torsion_basis)
    xPb, xQb, xPQb = kummer_basis_from_points(E0_kum, *b_torsion_basis)
    xPc, xQc, xPQc = kummer_basis_from_points(E0_kum, *c_torsion_basis)

    # Compute the diamond.
    sk_A, sk_B = randint(1, A - 1), randint(1, B - 1)
    xS_A = xQa.ladder_3_pt(xPa, xPQa, sk_A)  # = P + sk_A * Q
    xS_B = xQb.ladder_3_pt(xPb, xPQb, sk_B)  # = P + sk_B * Q
    phi_A = KummerLineIsogeny(E0_kum, xS_A, A)
    EA_kum = phi_A.codomain()
    EB_kum = KummerLineIsogeny(E0_kum, xS_B, B).codomain()

    xS_AB = phi_A(xS_B)
    EAB_kum = KummerLineIsogeny(EA_kum, xS_AB, B).codomain()

    # Keep the witness kernels and precomputed torsion data on the prover side.
    # The public statement consists only of the four curves.
    sk = (
        xS_A,
        xS_B,
        sk_B,
        (xPb, xQb, xPQb),
        (xPc, xQc, xPQc),
    )
    pk = (E0_kum, EA_kum, EB_kum, EAB_kum)
    return sk, pk


def prover(params, sk, pk):
    _, A, _, B, _, C, *_ = params
    (
        xS_A,
        xS_B,
        sk_B,
        (xPb, xQb, xPQb),
        (xPc, xQc, xPQc),
    ) = sk
    E0_kum, _, _, _ = pk

    # Generate a C-isogeny from E0
    sk_C = randint(0, C - 1)
    xS_C = xQc.ladder_3_pt(xPc, xPQc, sk_C)
    phi_C = KummerLineIsogeny(E0_kum, xS_C, C)
    EC_kum = phi_C.codomain()

    # Compute only the three back-face isogenies used by the seven-challenge
    # protocol. The fourth edge is derivable from psi_CA and psi_CB and no
    # longer has its own challenge.
    xK_psi_CA = phi_C(xS_A)
    psi_CA = KummerLineIsogeny(EC_kum, xK_psi_CA, A)
    EAC_kum = psi_CA.codomain()

    psi_CB = KummerLineIsogeny(EC_kum, phi_C(xS_B), B)
    EBC_kum = psi_CB.codomain()

    psi_ACB = KummerLineIsogeny(EAC_kum, psi_CA(phi_C(xS_B)), B)
    EABC_kum = psi_ACB.codomain()

    # Express the common B-kernel in a random B-torsion basis.
    xU0, xV0, xUV0, b_mat = random_kummer_basis(xPb, xQb, xPQb, B)
    xS_B_in_random_basis = vector(Zmod(B), [1, sk_B]) * b_mat.inverse()

    # Push the random B-torsion basis through phi_C and psi_CA.
    xUC = phi_C(xU0)
    xVC = phi_C(xV0)
    xUVC = phi_C(xUV0)
    xUAC = psi_CA(xUC)
    xVAC = psi_CA(xVC)
    xUVAC = psi_CA(xUVC)

    # Now, we must compute the dual of phi_C on EC and write it in a random basis.
    K_phi_C_dual = phi_C(xQc).curve_point()
    indep_c_torsion_pt = find_independent_point(EC_kum.curve(), K_phi_C_dual, C)
    xPc_spec, xQc_spec, xPQc_spec = kummer_basis_from_points(
        EC_kum, K_phi_C_dual, indep_c_torsion_pt
    )
    xPC, xQC, xPQC, c_mat = random_kummer_basis(
        xPc_spec, xQc_spec, xPQc_spec, C
    )
    xS_C_dual_in_random_basis = vector(Zmod(C), [1, 0]) * c_mat.inverse()

    xPAC = psi_CA(xPC)
    xQAC = psi_CA(xQC)
    xPQAC = psi_CA(xPQC)
    xPBC = psi_CB(xPC)
    xQBC = psi_CB(xQC)
    xPQBC = psi_CB(xPQC)
    xPABC = psi_ACB(xPAC)
    xQABC = psi_ACB(xQAC)
    xPQABC = psi_ACB(xPQAC)

    # Now we hash various public data to make the commitments.
    r0123 = randint(0, 2**256 - 1)
    r045 = randint(0, 2**256 - 1)
    r146 = randint(0, 2**256 - 1)
    r25 = randint(0, 2**256 - 1)
    r36 = randint(0, 2**256 - 1)
    r45 = randint(0, 2**256 - 1)
    r46 = randint(0, 2**256 - 1)
    r56 = randint(0, 2**256 - 1)
    r4 = randint(0, 2**256 - 1)

    h0123 = normalize_and_hash(r0123, xS_C_dual_in_random_basis)
    h045 = normalize_and_hash(r045, EC_kum, xPC, xQC, xPQC)
    h146 = normalize_and_hash(r146, EAC_kum, xPAC, xQAC, xPQAC)
    h25 = normalize_and_hash(r25, EBC_kum, xPBC, xQBC, xPQBC)
    h36 = normalize_and_hash(r36, EABC_kum, xPABC, xQABC, xPQABC)
    h45 = normalize_and_hash(r45, xUC, xVC, xUVC)
    h46 = normalize_and_hash(r46, xUAC, xVAC, xUVAC)
    h56 = normalize_and_hash(r56, xS_B_in_random_basis)
    h4 = normalize_and_hash(r4, xK_psi_CA)

    # Response algorithm in our case is a simple dictionary. In practice, we cannot send all of these together without leaking information. However, for this simple implementation, we keep it this way for ease of testing and clarity of the verification equations.
    # fmt: off
    responses = {
        0: (r0123, xS_C_dual_in_random_basis, r045, EC_kum, xPC, xQC, xPQC),
        1: (r0123, xS_C_dual_in_random_basis, r146, EAC_kum, xPAC, xQAC, xPQAC),
        2: (r0123, xS_C_dual_in_random_basis, r25, EBC_kum, xPBC, xQBC, xPQBC),
        3: (r0123, xS_C_dual_in_random_basis, r36, EABC_kum, xPABC, xQABC, xPQABC),
        4: (r045, EC_kum, xPC, xQC, xPQC, r146, EAC_kum, xPAC, xQAC, xPQAC, r45, xUC, xVC, xUVC, r46, xUAC, xVAC, xUVAC, r4, xK_psi_CA),
        5: (r045, EC_kum, xPC, xQC, xPQC, r25, EBC_kum, xPBC, xQBC, xPQBC, r45, xUC, xVC, xUVC, r56, xS_B_in_random_basis),
        6: (r146, EAC_kum, xPAC, xQAC, xPQAC, r36, EABC_kum, xPABC, xQABC, xPQABC, r46, xUAC, xVAC, xUVAC, r56, xS_B_in_random_basis),
    }
    # fmt: on

    commitment = (h0123, h045, h146, h25, h36, h45, h46, h56, h4)
    return commitment, responses


# Helper functions for the verifier's algorithm.
def verifier(params, pk, challenge, response, commitment):
    p, A, _, B, _, C, *_ = params
    E0_kum, EA_kum, EB_kum, EAB_kum = pk
    if challenge == 0:
        h0123, h045 = commitment[0], commitment[1]
        r0123, xS_C_dual_in_random_basis, r045, EC_kum, xPC, xQC, xPQC = response
        h0123_check = normalize_and_hash(r0123, xS_C_dual_in_random_basis)
        h045_check = normalize_and_hash(r045, EC_kum, xPC, xQC, xPQC)
        if h0123 != h0123_check or h045 != h045_check:
            return False

        EC = EC_kum.curve()

        if not is_supersingular_and_correct_characteristic_kummer(EC_kum, p):
            return False
        if not x_only_is_basis_cube(xPC, xQC, xPQC, C, EC):
            return False
        if not x_only_has_codomain(
            xS_C_dual_in_random_basis, (xPC, xQC, xPQC), C, EC_kum, E0_kum
        ):
            return False

    elif challenge == 1:
        h0123, h146 = commitment[0], commitment[2]
        r0123, xS_C_dual_in_random_basis, r146, EAC_kum, xPAC, xQAC, xPQAC = response
        h0123_check = normalize_and_hash(r0123, xS_C_dual_in_random_basis)
        h146_check = normalize_and_hash(r146, EAC_kum, xPAC, xQAC, xPQAC)
        if h0123 != h0123_check or h146 != h146_check:
            return False

        EAC = EAC_kum.curve()

        if not is_supersingular_and_correct_characteristic_kummer(EAC_kum, p):
            return False
        if not x_only_is_basis_cube(xPAC, xQAC, xPQAC, C, EAC):
            return False
        if not x_only_has_codomain(
            xS_C_dual_in_random_basis, (xPAC, xQAC, xPQAC), C, EAC_kum, EA_kum
        ):
            return False
    elif challenge == 2:
        h0123, h25 = commitment[0], commitment[3]
        r0123, xS_C_dual_in_random_basis, r25, EBC_kum, xPBC, xQBC, xPQBC = response
        h0123_check = normalize_and_hash(r0123, xS_C_dual_in_random_basis)
        h25_check = normalize_and_hash(r25, EBC_kum, xPBC, xQBC, xPQBC)
        if h0123 != h0123_check or h25 != h25_check:
            return False

        EBC = EBC_kum.curve()

        if not is_supersingular_and_correct_characteristic_kummer(EBC_kum, p):
            return False
        if not x_only_is_basis_cube(xPBC, xQBC, xPQBC, C, EBC):
            return False
        if not x_only_has_codomain(
            xS_C_dual_in_random_basis, (xPBC, xQBC, xPQBC), C, EBC_kum, EB_kum
        ):
            return False
    elif challenge == 3:
        h0123, h36 = commitment[0], commitment[4]
        r0123, xS_C_dual_in_random_basis, r36, EABC_kum, xPABC, xQABC, xPQABC = response
        h0123_check = normalize_and_hash(r0123, xS_C_dual_in_random_basis)
        h36_check = normalize_and_hash(r36, EABC_kum, xPABC, xQABC, xPQABC)
        if h0123 != h0123_check or h36 != h36_check:
            return False

        EABC = EABC_kum.curve()
        if not is_supersingular_and_correct_characteristic_kummer(EABC_kum, p):
            return False
        if not x_only_is_basis_cube(xPABC, xQABC, xPQABC, C, EABC):
            return False
        if not x_only_has_codomain(
            xS_C_dual_in_random_basis, (xPABC, xQABC, xPQABC), C, EABC_kum, EAB_kum
        ):
            return False
    elif challenge == 4:
        # fmt: off
        (r045, EC_kum, xPC, xQC, xPQC, r146, EAC_kum, xPAC, xQAC, xPQAC, r45, xUC, xVC, xUVC, r46, xUAC, xVAC, xUVAC, r4, xK_psi_CA) = response
        # fmt: on
        h045, h146, h45, h46, h4 = (
            commitment[1],
            commitment[2],
            commitment[5],
            commitment[6],
            commitment[8],
        )
        h045_check = normalize_and_hash(r045, EC_kum, xPC, xQC, xPQC)
        h146_check = normalize_and_hash(r146, EAC_kum, xPAC, xQAC, xPQAC)
        h45_check = normalize_and_hash(r45, xUC, xVC, xUVC)
        h46_check = normalize_and_hash(r46, xUAC, xVAC, xUVAC)
        h4_check = normalize_and_hash(r4, xK_psi_CA)
        if (
            h045 != h045_check
            or h146 != h146_check
            or h45 != h45_check
            or h46 != h46_check
            or h4 != h4_check
        ):
            return False

        EC = EC_kum.curve()

        if not is_supersingular_and_correct_characteristic_kummer(EC_kum, p):
            return False
        if not x_only_is_basis_cube(xPC, xQC, xPQC, C, EC):
            return False

        if not x_only_has_codomain_and_mapping_given_kernel(
            xK_psi_CA,
            A,
            EC_kum,
            EAC_kum,
            [xPC, xQC, xPQC, xUC, xVC, xUVC],
            [xPAC, xQAC, xPQAC, xUAC, xVAC, xUVAC],
        ):
            return False

    elif challenge == 5:
        # fmt: off
        (
            r045, EC_kum, xPC, xQC, xPQC, r25, EBC_kum, xPBC, xQBC, xPQBC,
            r45, xUC, xVC, xUVC, r56, S_B_in_random_basis
        ) = response
        # fmt: on
        h045, h25, h45, h56 = (
            commitment[1],
            commitment[3],
            commitment[5],
            commitment[7],
        )
        h045_check = normalize_and_hash(r045, EC_kum, xPC, xQC, xPQC)
        h25_check = normalize_and_hash(r25, EBC_kum, xPBC, xQBC, xPQBC)
        h45_check = normalize_and_hash(r45, xUC, xVC, xUVC)
        h56_check = normalize_and_hash(r56, S_B_in_random_basis)
        if (
            h045 != h045_check
            or h25 != h25_check
            or h45 != h45_check
            or h56 != h56_check
        ):
            return False

        EC = EC_kum.curve()

        if not is_supersingular_and_correct_characteristic_kummer(EC_kum, p):
            return False
        if not x_only_is_basis_cube(xPC, xQC, xPQC, C, EC):
            return False
        if not x_only_is_basis_cube(xUC, xVC, xUVC, B, EC):
            return False

        if not x_only_has_codomain_and_mapping(
            S_B_in_random_basis,
            (xUC, xVC, xUVC),
            B,
            EC_kum,
            EBC_kum,
            [xPC, xQC, xPQC],
            [xPBC, xQBC, xPQBC],
        ):
            return False
    elif challenge == 6:
        # fmt: off
        (
            r146, EAC_kum, xPAC, xQAC, xPQAC, r36, EABC_kum, xPABC, xQABC, xPQABC,
            r46, xUAC, xVAC, xUVAC, r56, S_B_in_random_basis
        ) = response
        # fmt: on
        h146, h36, h46, h56 = (
            commitment[2],
            commitment[4],
            commitment[6],
            commitment[7],
        )
        h146_check = normalize_and_hash(r146, EAC_kum, xPAC, xQAC, xPQAC)
        h36_check = normalize_and_hash(r36, EABC_kum, xPABC, xQABC, xPQABC)
        h46_check = normalize_and_hash(r46, xUAC, xVAC, xUVAC)
        h56_check = normalize_and_hash(r56, S_B_in_random_basis)
        if h146 != h146_check or h36 != h36_check or h46 != h46_check or h56 != h56_check:
            return False

        EAC = EAC_kum.curve()

        if not is_supersingular_and_correct_characteristic_kummer(EAC_kum, p):
            return False
        if not x_only_is_basis_cube(xPAC, xQAC, xPQAC, C, EAC):
            return False
        if not x_only_is_basis_cube(xUAC, xVAC, xUVAC, B, EAC):
            return False

        if not x_only_has_codomain_and_mapping(
            S_B_in_random_basis,
            (xUAC, xVAC, xUVAC),
            B,
            EAC_kum,
            EABC_kum,
            [xPAC, xQAC, xPQAC],
            [xPABC, xQABC, xPQABC],
        ):
            return False
    else:
        return False

    return True


class FiatShamir:
    def __init__(self, params):
        self.params = params
        self.num_reps = params[7]

    def _challenges(self, pk, commitments):
        p, A, _, B, _, C, *_ = self.params
        statement_hash = normalize_and_hash(p, A, B, C, *pk)
        transcript = "|".join(
            ["cube-fiat-shamir", statement_hash]
            + [value for commitment in commitments for value in commitment]
        )
        seed = hashlib.sha256(transcript.encode()).digest()

        challenges = []
        counter = 0
        rejection_bound = 256 - (256 % NUM_CHALLENGES)
        while len(challenges) < len(commitments):
            block = hashlib.sha256(seed + counter.to_bytes(4, "big")).digest()
            challenges.extend(
                value % NUM_CHALLENGES for value in block if value < rejection_bound
            )
            counter += 1
        return challenges[: len(commitments)]

    def prover(self, sk, pk):
        """Constructs a non-interactive proof with the configured repetitions."""
        rounds = [prover(self.params, sk, pk) for _ in range(self.num_reps)]
        commitments = [commitment for commitment, _ in rounds]
        challenges = self._challenges(pk, commitments)

        return [
            (commitment, responses[challenge])
            for (commitment, responses), challenge in zip(rounds, challenges)
        ]

    def verifier(self, pk, proof):
        """Verifies a non-interactive proof with the configured repetitions."""
        if len(proof) != self.num_reps:
            return False

        commitments = [commitment for commitment, _ in proof]
        challenges = self._challenges(pk, commitments)
        return all(
            verifier(self.params, pk, challenge, response, commitment)
            for (commitment, response), challenge in zip(proof, challenges)
        )


if __name__ == "__main__":
    from cube_params import CUBE_128_PARAMS

    fiat_shamir = FiatShamir(CUBE_128_PARAMS)
    sk, pk = key_gen(CUBE_128_PARAMS)
    prover_start = time.time()
    proof = fiat_shamir.prover(sk, pk)
    prover_end = time.time()
    assert len(proof) == CUBE_128_PARAMS[7]
    assert fiat_shamir.verifier(pk, proof)
    verifier_end = time.time()

    print("Fiat-Shamir test passed")
    print(f"Fiat-Shamir prover: {prover_end - prover_start:.2f}s")
    print(f"Fiat-Shamir verifier: {verifier_end - prover_end:.2f}s")
