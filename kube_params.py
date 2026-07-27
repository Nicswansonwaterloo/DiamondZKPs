from sage.all import GF, Integer, ceil, gcd, is_prime, log_b, previous_prime


def generate_params(security_level=128, search_radius=20, max_cofactor=None):
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

    max_cofactor = max_cofactor or security_level + 2 * search_radius
    candidates = []
    for e2 in range(e2_needed, e2_needed + search_radius):
        for e3 in range(e3_needed, e3_needed + search_radius):
            for c in range(1, max_cofactor + 1):
                if c % 3 == 0 or c % 2 == 0:
                    continue
                p = 4 * Integer(2) ** e2 * Integer(3) ** e3 * Integer(c) - 1
                candidates.append((p, e2, e3, c))

    selected = next(
        (candidate for candidate in sorted(candidates) if is_prime(candidate[0])),
        None,
    )
    if selected is None:
        raise ValueError("No prime found in the requested exponent search window.")

    _, e2, e3, c = selected
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
    Integer(4 * 2**238 * 3**297 * 25 - 1),
    Integer(2**238),
    Integer(238),
    Integer(3**297),
    Integer(297),
    Integer(25),
    Integer(
        220855883097298041197912187592864814478435487109452369765200775161546677
    ),
    Integer(
        220855883097298041197912187592864814478435487109452369765200775161608267
    ),
    Integer(398),
    GF(
        (4 * 2**238 * 3**297 * 25 - 1) ** 2,
        modulus=[1, 0, 1],
        names="i",
    ),
]


# Small research parameters used by kube_optimized.py's five-challenge test.
KUBE_TEST_PARAMS = [
    Integer(4 * 2**32 * 3**38 * 5 - 1),
    Integer(2**32),
    Integer(32),
    Integer(3**38),
    Integer(38),
    Integer(5),
    Integer(2147482367),
    Integer(2147484929),
    Integer(50),
    GF(
        (4 * 2**32 * 3**38 * 5 - 1) ** 2,
        modulus=[1, 0, 1],
        names="i",
    ),
]


if __name__ == "__main__":
    generate_params(security_level=128, search_radius=20)
