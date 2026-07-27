from sage.all import GF, Integer, ceil, floor, gcd, is_prime, log_b, previous_prime


def generate_params(security_level=128, search_radius=10, heuristic=False):
    """
    Search for Kani parameters with ``p = 4 * 2^e2 * 3^e3 - 1``. If ``heuristic`` is True,
    we take e3 to be roughly 3/2 * e2, otherwise we take e3 approx 3 e2.
    """
    num_reps = ceil(security_level * log_b(2, 3 / 2))
    memory_limit = security_level * (3 / 4)  # A rough estimate, on max memory limit available.

    # Assume the best attack is square-root time in each corresponding search space, consting square root memory as well. With seach space S and memory limit m, collision finding takes S^1.5 / m^0.5
    # time (approx).
    e2_needed = ceil((4 / 3) * (security_level + (memory_limit // 2)))
    if heuristic:
        e3_needed = ceil((3 / 2) * e2_needed * log_b(2, 3))
    else:
        e3_needed = ceil(3 * e2_needed * log_b(2, 3))

    # Add aditional contraint for implementation efficiency.
    def additional_constraint(p):
        return p % 4 == 3

    minimal_p = None
    best_exponents = None
    best_cofactor = None
    for e2 in range(e2_needed, e2_needed + search_radius):
        for e3 in range(e3_needed, e3_needed + search_radius):
            # for c in range(1, security_level + 1 + 2 * search_radius): # c is a small cofactor
            for c in range(1, 2):
                if c % 3 == 0 or c % 2 == 0:
                    continue

                p = 4 * Integer(2) ** e2 * Integer(3) ** e3 * Integer(c) - 1
                if is_prime(p) and (minimal_p is None or p < minimal_p) and additional_constraint(p):
                    minimal_p = p
                    best_exponents = (e2, e3)
                    best_cofactor = c

    if best_exponents is None:
        raise ValueError("No prime found in the requested exponent search window.")

    e2, e3 = best_exponents
    c = best_cofactor
    N = Integer(2) ** e2
    M = Integer(3) ** e3
    p = 4 * N * M * c - 1

    # While not explicitly necessary, we also provide A and B such that A + B = N and gcd(A * B, 3) = 1.
    A = previous_prime(N // 2)
    while not is_prime(N - A) or gcd(A * (N - A), 3) != 1:
        A = previous_prime(A)
    B = N - A

    print("Generated parameters:\n")
    print(
        f"Integer(4 * 2**{e2} * 3**{e3} * {c} - 1),\n"
        f"Integer(2**{e2}),\n"
        f"Integer({e2}),\n"
        f"Integer(3**{e3}),\n"
        f"Integer({e3}),\n"
        f"Integer({c}),\n"
        f"Integer({A}),\n"
        f"Integer({B}),\n"
        f"Integer({num_reps}),\n"
        f"GF((4 * 2**{e2} * 3**{e3} * {c} - 1)**2, modulus=[1, 0, 1], names='i')\n"
    )
    return p, N, e2, M, e3, c, A, B, num_reps, GF(p**2, modulus=[1, 0, 1], names="i")


# 128-bit parameters, heuristic.
KANI_128_PARAMS_HEUR = [
    Integer(4 * 2**244 * 3**245 * 1 - 1),
    Integer(2**244),
    Integer(244),
    Integer(3**245),
    Integer(245),
    Integer(1),
    Integer(14134776518227074636666380005943348126619871175004951664972849610340947393),
    Integer(14134776518227074636666380005943348126619871175004951664972849610340969023),
    Integer(219),
    GF((4 * 2**244 * 3**245 * 1 - 1)**2, modulus=[1, 0, 1], names='i')
]

# Small 64-bit-security research parameters (non-heuristic).
KANI_TEST_PARAMS_64 = [
    Integer(4 * 2**125 * 3**229 * 1 - 1),
    Integer(2**125),
    Integer(125),
    Integer(3**229),
    Integer(229),
    Integer(1),
    Integer(21267647932558653966460912964485509379),
    Integer(21267647932558653966460912964485517053),
    Integer(110),
    GF((4 * 2**125 * 3**229 * 1 - 1)**2, modulus=[1, 0, 1], names='i')
]

if __name__ == "__main__":
    generate_params(security_level=128, search_radius=30, heuristic=True)
