from sage.all import GF, Integer, ceil, gcd, is_prime, log_b, previous_prime


def generate_params(security_level=128, search_radius=20):
    """
    Search for Kube parameters with ``p = 4 * 2^e2 * 3^e3 * c - 1``.

    The 2-power N controls the non-smooth Kani diamond, while the 3-power C is
    sized at roughly N^2 for the DSSP reduction of the fifth challenge.
    """
    memory_limit = security_level * (3 / 4)
    num_reps = ceil(security_level * log_b(2, 5 / 4))

    # Use the same time-memory estimate as cube_params.py and kani_params.py.
    e2_needed = ceil((4 / 3) * (security_level + (memory_limit // 2)))
    e3_needed = ceil(2 * e2_needed * log_b(2, 3))

    minimal_p = None
    best_exponents = None
    best_cofactor = None
    for e2 in range(e2_needed, e2_needed + search_radius):
        for e3 in range(e3_needed, e3_needed + search_radius):
            # The current RanIso precomputation supports no extra cofactor.
            for c in range(1, 2):
                p = 4 * Integer(2) ** e2 * Integer(3) ** e3 * Integer(c) - 1
                if is_prime(p) and (minimal_p is None or p < minimal_p):
                    minimal_p = p
                    best_exponents = (e2, e3)
                    best_cofactor = c

    if best_exponents is None:
        raise ValueError("No prime found in the requested exponent search window.")

    e2, e3 = best_exponents
    c = best_cofactor
    N = Integer(2) ** e2
    C = Integer(3) ** e3
    p = 4 * N * C * c - 1

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
        f"GF((4 * 2**{e2} * 3**{e3} * {c} - 1)**2, "
        "modulus=[1, 0, 1], names='i')\n"
    )
    return p, N, e2, C, e3, c, A, B, num_reps, GF(
        p**2, modulus=[1, 0, 1], names="i"
    )


# Generated with generate_params(security_level=128, search_radius=20).
KUBE_128_PARAMS = [
    Integer(4 * 2**239 * 3**303 - 1),
    Integer(2**239),
    Integer(239),
    Integer(3**303),
    Integer(303),
    Integer(1),
    Integer(
        441711766194596082395824375185729628956870974218904739530401550323115701
    ),
    Integer(
        441711766194596082395824375185729628956870974218904739530401550323194187
    ),
    Integer(398),
    GF(
        (4 * 2**239 * 3**303 - 1) ** 2,
        modulus=[1, 0, 1],
        names="i",
    ),
]


# Small research parameters used by kube_optimized.py's five-challenge test.
KUBE_TEST_PARAMS = [
    Integer(4 * 2**39 * 3**40 - 1),
    Integer(2**39),
    Integer(39),
    Integer(3**40),
    Integer(40),
    Integer(1),
    Integer(274877904601),
    Integer(274877909287),
    Integer(50),
    GF(
        (4 * 2**39 * 3**40 - 1) ** 2,
        modulus=[1, 0, 1],
        names="i",
    ),
]


if __name__ == "__main__":
    generate_params(security_level=128, search_radius=20)
