from sage.all import GF, EllipticCurve, Integer, ceil, is_prime, log_b


def generate_params(security_level=128, search_radius=10):
    """
    Search for a prime of the form ``p = 2^e2 * 3^e3 * 5^e5 - 1`` for a
    security level given as a bit size.
    This script assumes:
    - The best attack on DSSP is square-root in the degree.
    """
    memory_limit = security_level * (3 / 4) # A rough estimate, on max memory limit available.
    num_reps = ceil(security_level * log_b(2, 7 / 6))

    # Assume the best attack is square-root time in each corresponding search space, consting square root memory as well. With seach space S and memory limit m, collision finding takes S^1.5 / m^0.5
    # time (approx).
    e2_needed = ceil((4 / 3) * (security_level + (memory_limit // 2)))
    e3_needed = ceil(e2_needed * log_b(2, 3))
    e5_needed = ceil(e2_needed * log_b(2, 5))

    # Add aditional contraint for implementation efficiency.
    def additional_constraint(p):
        return p % 4 == 3

    minimal_p = None
    best_exponents = None

    for e2 in range(e2_needed, e2_needed + search_radius):
        for e3 in range(e3_needed, e3_needed + search_radius):
            for e5 in range(e5_needed, e5_needed + search_radius):
                p = 2**e2 * 3**e3 * 5**e5 - 1
                if (
                    is_prime(p)
                    and (minimal_p is None or p < minimal_p)
                    and additional_constraint(p)
                ):
                    minimal_p = p
                    best_exponents = (e2, e3, e5)

    if best_exponents is None:
        raise ValueError("No prime found in the requested exponent search window.")

    e2_min, e3_min, e5_min = best_exponents

    p = 2**e2_min * 3**e3_min * 5**e5_min - 1
    A = 2**e2_min
    B = 3**e3_min
    C = 5**e5_min

    Fp2 = GF(p**2, modulus=[1, 0, 1], names="i")
    E0 = EllipticCurve(Fp2, [0, 1]).montgomery_model()

    print("Generated parameters:")
    print(
        f"2**{e2_min} * 3**{e3_min} * 5**{e5_min} - 1,\n"
        f"2**{e2_min},\n"
        f"{e2_min},\n"
        f"3**{e3_min},\n"
        f"{e3_min},\n"
        f"5**{e5_min},\n"
        f"{e5_min},\n"
        f"{num_reps},\n"
        f"GF((2**{e2_min} * 3**{e3_min} * 5**{e5_min} - 1)**2, modulus=[1, 0, 1], names='i')\n"
    )

    return p, A, B, C, num_reps, Fp2, E0


# Ran using generate_params(security_level=128, search_radius=20)
CUBE_128_PARAMS = [
    Integer(2**240 * 3**149 * 5**103 - 1),
    Integer(2**240),
    Integer(240),
    Integer(3**149),
    Integer(149),
    Integer(5**103),
    Integer(103),
    Integer(576),
    GF((2**240 * 3**149 * 5**103 - 1)**2, modulus=[1, 0, 1], names='i')
]

CUBE_TEST_PARAMS = [
    Integer(2**63 * 3**49 * 5**39 - 1),
    Integer(2**63),
    Integer(63),
    Integer(3**49),
    Integer(49),
    Integer(5**39),
    Integer(39),
    Integer(216),
    GF(Integer(2**63 * 3**49 * 5**39 - 1) ** 2, modulus=[1, 0, 1], names="i"),
]

if __name__ == "__main__":
    generate_params(security_level=128, search_radius=20)
