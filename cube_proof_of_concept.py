from sage.all import (
    randint,
)

from helpers.ec_utils import (
    has_codomain,
    has_codomain_and_mapping,
    is_basis_cube,
    is_supersingular_and_correct_characteristic,
    random_supersingular_curve,
    randomize_basis,
)
from helpers.helpers import normalize_and_hash
from vendors.Theta_SageMath.utilities.supersingular import torsion_basis


def key_gen(params):
    """Constructs a random isogeny diamond."""
    p, A, _, B, _, C, _, num_reps, Fp2 = params

    # Pick a random E0 and fix torsion bases for E0.
    E0 = random_supersingular_curve(p)
    a_torsion_basis = torsion_basis(E0, A)
    b_torsion_basis = torsion_basis(E0, B)
    c_torsion_basis = torsion_basis(E0, C)

    # Compute out statment to prove (the isogeny diamond).
    sk_A, sk_B = randint(1, A - 1), randint(1, B - 1)
    S_A = a_torsion_basis[0] + sk_A * a_torsion_basis[1]
    S_B = b_torsion_basis[0] + sk_B * b_torsion_basis[1]
    phi_A = E0.isogeny(S_A, algorithm="factored")
    phi_B = E0.isogeny(S_B, algorithm="factored")
    EA = phi_A.codomain()
    EB = phi_B.codomain()
    S_AB = phi_A(S_B)
    S_BA = phi_B(S_A)
    psi_AB = EA.isogeny(S_AB, algorithm="factored")
    psi_BA = EB.isogeny(S_BA, algorithm="factored")
    EAB = psi_BA.codomain()
    assert EAB == psi_AB.codomain()

    # Secret info is the isogenies in the diamond, and the integers representing the secret keys in the fixed torsion bases.
    # We bloat the secret key as the isogenies themselves for ease of implementation of the prover.
    sk = (phi_A, phi_B, psi_AB, psi_BA, S_A, S_B, S_AB, S_BA, sk_A, sk_B)
    pk = (E0, EA, EB, EAB, a_torsion_basis, b_torsion_basis, c_torsion_basis)
    return sk, pk


def prover(params, sk, pk):
    p, A, _, B, _, C, _, num_reps, Fp2 = params
    phi_A, phi_B, psi_AB, _, S_A, S_B, S_AB, S_BA, sk_A, sk_B = sk
    E0, EA, EB, EAB, a_torsion_basis, b_torsion_basis, c_torsion_basis = pk

    # Generate a C-isogeny from E0. This isogeny along with the diamond form the cube
    S_C = c_torsion_basis[0] + randint(0, C - 1) * c_torsion_basis[1]
    phi_C = E0.isogeny(S_C, algorithm="factored")
    EC = phi_C.codomain()

    # Push the C-isogeny around.
    psi_CA = EC.isogeny(phi_C(S_A), algorithm="factored")
    psi_CB = EC.isogeny(phi_C(S_B), algorithm="factored")
    psi_AC = EA.isogeny(phi_A(S_C), algorithm="factored")
    psi_BC = EB.isogeny(phi_B(S_C), algorithm="factored")

    EBC = psi_BC.codomain()
    EAC = psi_AC.codomain()
    assert EBC == psi_CB.codomain()
    assert EAC == psi_CA.codomain()

    # Compute the last three edges of the cube
    S_AC = phi_A(S_C)
    psi_ABC = EAB.isogeny(psi_AB(S_AC), algorithm="factored")
    psi_BCA = EBC.isogeny(psi_BC(S_BA), algorithm="factored")
    psi_ACB = EAC.isogeny(psi_AC(S_AB), algorithm="factored")
    EABC = psi_ABC.codomain()
    assert EABC == psi_BCA.codomain() == psi_ACB.codomain()

    # Pick random bases for the A, B torsion, and get coefficients of the phi_A and phi_B in this basis.
    a_random_basis, _, S_A_in_random_basis = randomize_basis(a_torsion_basis, A, [1, sk_A])
    b_random_basis, _, S_B_in_random_basis = randomize_basis(b_torsion_basis, B, [1, sk_B])

    # With the formed cube and random basis, push the basis around the cube.
    R0 = E0(a_random_basis[0])
    S0 = E0(a_random_basis[1])
    RC = phi_C(R0)
    SC = phi_C(S0)
    RBC = psi_CB(RC)
    SBC = psi_CB(SC)

    U0 = E0(b_random_basis[0])
    V0 = E0(b_random_basis[1])
    UC = phi_C(U0)
    VC = phi_C(V0)
    UAC = psi_CA(UC)
    VAC = psi_CA(VC)

    # Pick random bases for the C torsion and write the dual of phi_C in that basis.
    # First we form a special basis where the first point is the dual of phi_C's kernel, then we randomize it.
    phi_C_dual_ker = phi_C(c_torsion_basis[1])
    EC.set_order((p + 1) ** 2)  # Needed so .torsion_basis does not take too long.
    c_torsion_basis_EC = EC.torsion_basis(C)
    independent_c_torsion_point = c_torsion_basis_EC[0] + c_torsion_basis_EC[1] * randint(1, C - 1)
    while independent_c_torsion_point.weil_pairing(phi_C_dual_ker, C) ** (C // 5) == 1:
        independent_c_torsion_point = c_torsion_basis_EC[0] + c_torsion_basis_EC[1] * randint(
            1, C - 1
        )
    c_torsion_basis_special = [phi_C_dual_ker, independent_c_torsion_point]
    c_random_basis, _, phi_C_dual_ker_in_random_basis = randomize_basis(
        c_torsion_basis_special, C, [1, 0]
    )
    
    # Finally, push the random c_basis around the cube as well.
    PC = c_random_basis[0]
    QC = c_random_basis[1]
    PAC = psi_CA(PC)
    QAC = psi_CA(QC)
    PBC = psi_CB(PC)
    QBC = psi_CB(QC)
    PABC = psi_BCA(PBC)
    QABC = psi_BCA(QBC)

    # Now we hash various data buckets to make the commitments.
    # Note that the indices correspond the the challanges for which the bucket is revealed.
    r0123 = randint(0, 2**256 - 1)
    r045 = randint(0, 2**256 - 1)
    r146 = randint(0, 2**256 - 1)
    r257 = randint(0, 2**256 - 1)
    r367 = randint(0, 2**256 - 1)
    r45 = randint(0, 2**256 - 1)
    r46 = randint(0, 2**256 - 1)
    r47 = randint(0, 2**256 - 1)
    r56 = randint(0, 2**256 - 1)
    r57 = randint(0, 2**256 - 1)  # 10 nonces

    h0123 = normalize_and_hash(r0123, phi_C_dual_ker_in_random_basis)
    h045 = normalize_and_hash(r045, EC, PC, QC)
    h146 = normalize_and_hash(r146, EAC, PAC, QAC)
    h257 = normalize_and_hash(r257, EBC, PBC, QBC)
    h367 = normalize_and_hash(r367, EABC, PABC, QABC)
    h45 = normalize_and_hash(r45, RC, SC, UC, VC)
    h46 = normalize_and_hash(r46, UAC, VAC)
    h47 = normalize_and_hash(r47, S_A_in_random_basis)
    h56 = normalize_and_hash(r56, S_B_in_random_basis)
    h57 = normalize_and_hash(r57, RBC, SBC)

    # Response algorithm in our case is a simple dictionary. In practice, we cannot send all of these together without leaking information. However, for this simple implementation, we keep it this way for ease of testing and clarity of the verification.
    # fmt: off
    responses = {
        0: (r0123, phi_C_dual_ker_in_random_basis, r045, EC, PC, QC),
        1: (r0123, phi_C_dual_ker_in_random_basis, r146, EAC, PAC, QAC),
        2: (r0123, phi_C_dual_ker_in_random_basis, r257, EBC, PBC, QBC),
        3: (r0123, phi_C_dual_ker_in_random_basis, r367, EABC, PABC, QABC),
        4: (r045, EC, PC, QC, r146, EAC, PAC, QAC, r45, RC, SC, UC, VC, r46, UAC, VAC, r47, S_A_in_random_basis),
        5: (r045, EC, PC, QC, r257, EBC, PBC, QBC, r45, RC, SC, UC, VC, r56, S_B_in_random_basis, r57, RBC, SBC),
        6: (r146, EAC, PAC, QAC, r367, EABC, PABC, QABC, r46, UAC, VAC, r56, S_B_in_random_basis),
        7: (r257, EBC, PBC, QBC, r367, EABC, PABC, QABC, r47, S_A_in_random_basis, r57, RBC, SBC),
    }
    # fmt: on

    commitment = (h0123, h045, h146, h257, h367, h45, h46, h47, h56, h57)
    return commitment, responses


def verifier(params, pk, challenge, response, commitment):
    p, A, _, B, _, C, _, num_reps, Fp2 = params
    E0, EA, EB, EAB, a_torsion_basis, b_torsion_basis, c_torsion_basis = pk
    if challenge == 0:
        # In each challange we first check the hashes are correct for the response.
        h0123 = commitment[0]
        h045 = commitment[1]
        r0123, phi_C_dual_ker_in_random_basis, r045, EC, PC, QC = response
        h0123_check = normalize_and_hash(r0123, phi_C_dual_ker_in_random_basis)
        h045_check = normalize_and_hash(r045, EC, PC, QC)
        C_basis = (PC, QC)
        if h0123 != h0123_check or h045 != h045_check:
            return False

        # Then we check various properties as outlined in the paper.
        if not is_supersingular_and_correct_characteristic(EC, p):
            return False
        if not is_basis_cube(PC, QC, C, EC):
            return False
        if not has_codomain(phi_C_dual_ker_in_random_basis, C_basis, C, EC, E0):
            return False
    elif challenge == 1:
        h0123 = commitment[0]
        h146 = commitment[2]
        r0123, phi_C_dual_ker_in_random_basis, r146, EAC, PAC, QAC = response
        h0123_check = normalize_and_hash(r0123, phi_C_dual_ker_in_random_basis)
        h146_check = normalize_and_hash(r146, EAC, PAC, QAC)
        C_basis = (PAC, QAC)
        if h0123 != h0123_check or h146 != h146_check:
            return False

        if not is_supersingular_and_correct_characteristic(EAC, p):
            return False
        if not is_basis_cube(PAC, QAC, C, EAC):
            return False
        if not has_codomain(phi_C_dual_ker_in_random_basis, C_basis, C, EAC, EA):
            return False
    elif challenge == 2:
        h0123 = commitment[0]
        h257 = commitment[3]
        r0123, phi_C_dual_ker_in_random_basis, r257, EBC, PBC, QBC = response
        h0123_check = normalize_and_hash(r0123, phi_C_dual_ker_in_random_basis)
        h257_check = normalize_and_hash(r257, EBC, PBC, QBC)
        C_basis = (PBC, QBC)
        if h0123 != h0123_check or h257 != h257_check:
            return False

        if not is_supersingular_and_correct_characteristic(EBC, p):
            return False
        if not is_basis_cube(PBC, QBC, C, EBC):
            return False
        if not has_codomain(phi_C_dual_ker_in_random_basis, C_basis, C, EBC, EB):
            return False
    elif challenge == 3:
        h0123 = commitment[0]
        h367 = commitment[4]
        r0123, phi_C_dual_ker_in_random_basis, r367, EABC, PABC, QABC = response
        h0123_check = normalize_and_hash(r0123, phi_C_dual_ker_in_random_basis)
        h367_check = normalize_and_hash(r367, EABC, PABC, QABC)
        C_basis = (PABC, QABC)
        if h0123 != h0123_check or h367 != h367_check:
            return False

        if not is_supersingular_and_correct_characteristic(EABC, p):
            return False
        if not is_basis_cube(PABC, QABC, C, EABC):
            return False
        if not has_codomain(phi_C_dual_ker_in_random_basis, C_basis, C, EABC, EAB):
            return False
    elif challenge == 4:
        # fmt: off
        (r045, EC, PC, QC, r146, EAC, PAC, QAC, r45, RC, SC, UC, VC, r46, UAC, VAC, r47, S_A_in_random_basis) = response
        # fmt: on
        h045, h146, h45, h46, h47 = (
            commitment[1],
            commitment[2],
            commitment[5],
            commitment[6],
            commitment[7],
        )
        h045_check = normalize_and_hash(r045, EC, PC, QC)
        h146_check = normalize_and_hash(r146, EAC, PAC, QAC)
        h45_check = normalize_and_hash(r45, RC, SC, UC, VC)
        h46_check = normalize_and_hash(r46, UAC, VAC)
        h47_check = normalize_and_hash(r47, S_A_in_random_basis)
        if (
            h045 != h045_check
            or h146 != h146_check
            or h45 != h45_check
            or h46 != h46_check
            or h47 != h47_check
        ):
            return False
        if not is_supersingular_and_correct_characteristic(EC, p):
            return False
        if not is_supersingular_and_correct_characteristic(EAC, p):
            return False
        if not is_basis_cube(PC, QC, C, EC):
            return False
        if not is_basis_cube(RC, SC, A, EC):
            return False
        if not is_basis_cube(UC, VC, B, EC):
            return False
        A_basis = (RC, SC)
        if not has_codomain_and_mapping(
            S_A_in_random_basis,
            A_basis,
            A,
            EC,
            EAC,
            [PC, QC, UC, VC],
            [PAC, QAC, UAC, VAC],
        ):
            return False
    elif challenge == 5:
        # fmt: off
        (
            r045, EC, PC, QC, r257, EBC, PBC, QBC, r45, RC, SC, UC, VC,
            r56, S_B_in_random_basis, r57, RBC, SBC
        ) = response
        # fmt: on
        h045, h257, h45, h56, h57 = (
            commitment[1],
            commitment[3],
            commitment[5],
            commitment[8],
            commitment[9],
        )
        h045_check = normalize_and_hash(r045, EC, PC, QC)
        h257_check = normalize_and_hash(r257, EBC, PBC, QBC)
        h45_check = normalize_and_hash(r45, RC, SC, UC, VC)
        h56_check = normalize_and_hash(r56, S_B_in_random_basis)
        h57_check = normalize_and_hash(r57, RBC, SBC)
        if (
            h045 != h045_check
            or h257 != h257_check
            or h45 != h45_check
            or h56 != h56_check
            or h57 != h57_check
        ):
            return False

        if not is_supersingular_and_correct_characteristic(EC, p):
            return False
        if not is_supersingular_and_correct_characteristic(EBC, p):
            return False
        if not is_basis_cube(PC, QC, C, EC):
            return False
        if not is_basis_cube(RC, SC, A, EC):
            return False
        if not is_basis_cube(UC, VC, B, EC):
            return False
        B_basis = (UC, VC)
        if not has_codomain_and_mapping(
            S_B_in_random_basis,
            B_basis,
            B,
            EC,
            EBC,
            [PC, QC, RC, SC],
            [PBC, QBC, RBC, SBC],
        ):
            return False
    elif challenge == 6:
        # fmt: off
        (
            r146, EAC, PAC, QAC, r367, EABC, PABC, QABC,
            r46, UAC, VAC, r56, S_B_in_random_basis
        ) = response
        # fmt: on
        h146, h367, h46, h56 = (
            commitment[2],
            commitment[4],
            commitment[6],
            commitment[8],
        )
        h146_check = normalize_and_hash(r146, EAC, PAC, QAC)
        h367_check = normalize_and_hash(r367, EABC, PABC, QABC)
        h46_check = normalize_and_hash(r46, UAC, VAC)
        h56_check = normalize_and_hash(r56, S_B_in_random_basis)
        if h146 != h146_check or h367 != h367_check or h46 != h46_check or h56 != h56_check:
            return False

        if not is_supersingular_and_correct_characteristic(EAC, p):
            return False
        if not is_supersingular_and_correct_characteristic(EABC, p):
            return False
        if not is_basis_cube(PAC, QAC, C, EAC):
            return False
        if not is_basis_cube(UAC, VAC, B, EAC):
            return False
        B_basis = (UAC, VAC)
        if not has_codomain_and_mapping(
            S_B_in_random_basis, B_basis, B, EAC, EABC, [PAC, QAC], [PABC, QABC]
        ):
            return False
    elif challenge == 7:
        # fmt: off
        (r257, EBC, PBC, QBC, r367, EABC, PABC, QABC, r47, S_A_in_random_basis, r57, RBC, SBC) = response
        # fmt: on
        h257, h367, h47, h57 = (
            commitment[3],
            commitment[4],
            commitment[7],
            commitment[9],
        )
        h257_check = normalize_and_hash(r257, EBC, PBC, QBC)
        h367_check = normalize_and_hash(r367, EABC, PABC, QABC)
        h47_check = normalize_and_hash(r47, S_A_in_random_basis)
        h57_check = normalize_and_hash(r57, RBC, SBC)
        if h257 != h257_check or h367 != h367_check or h47 != h47_check or h57 != h57_check:
            return False

        if not is_supersingular_and_correct_characteristic(EBC, p):
            return False
        if not is_supersingular_and_correct_characteristic(EABC, p):
            return False
        if not is_basis_cube(PBC, QBC, C, EBC):
            return False
        if not is_basis_cube(RBC, SBC, A, EBC):
            return False
        A_basis = (RBC, SBC)
        if not has_codomain_and_mapping(
            S_A_in_random_basis, A_basis, A, EBC, EABC, [PBC, QBC], [PABC, QABC]
        ):
            return False

    return True
