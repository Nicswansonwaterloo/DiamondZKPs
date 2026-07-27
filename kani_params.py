from sage.all import GF, Integer, ceil, floor, gcd, is_prime, log_b, previous_prime


def generate_params(
    security_level=128,
    search_radius=10,
    heuristic=False,
    max_cofactor=None,
):
    """
    Search for Kani parameters with ``p = 4 * 2^e2 * 3^e3 * c - 1``. If ``heuristic`` is True,
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

    max_cofactor = max_cofactor or security_level + 2 * search_radius
    candidates = []
    for e2 in range(e2_needed, e2_needed + search_radius):
        for e3 in range(e3_needed, e3_needed + search_radius):
            for c in range(1, max_cofactor + 1):
                if c % 3 == 0 or c % 2 == 0:
                    continue

                p = 4 * Integer(2) ** e2 * Integer(3) ** e3 * Integer(c) - 1
                if additional_constraint(p):
                    candidates.append((p, e2, e3, c))

    selected = next(
        (candidate for candidate in sorted(candidates) if is_prime(candidate[0])),
        None,
    )
    if selected is None:
        raise ValueError("No prime found in the requested exponent search window.")

    _, e2, e3, c = selected
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


# 128-bit parameters.
KANI_128_PARAMS = [
    Integer(4 * 2**237 * 3**445 * 25 - 1),
    Integer(2**237),
    Integer(237),
    Integer(3**445),
    Integer(445),
    Integer(25),
    Integer(110427941548649020598956093796432407239217743554726184882600387580783369),
    Integer(110427941548649020598956093796432407239217743554726184882600387580794103),
    Integer(219),
    GF((4 * 2**237 * 3**445 * 25 - 1)**2, modulus=[1, 0, 1], names='i')
]


# 128-bit parameters, heuristic.
KANI_128_PARAMS_HEUR = [
    Integer(4 * 2**236 * 3**223 * 43 - 1),
    Integer(2**236),
    Integer(236),
    Integer(3**223),
    Integer(223),
    Integer(43),
    Integer(
        55213970774324510299478046898216203619608871777363092441300193790377103
    ),
    Integer(
        55213970774324510299478046898216203619608871777363092441300193790411633
    ),
    Integer(219),
    GF(
        (4 * 2**236 * 3**223 * 43 - 1) ** 2,
        modulus=[1, 0, 1],
        names="i",
    ),
]

# Small 64-bit-security research parameters (non-heuristic).
KANI_TEST_PARAMS = [
    Integer(4 * 2**61 * 3**56 * 19 - 1),
    Integer(2**61),
    Integer(61),
    Integer(3**56),
    Integer(56),
    Integer(19),
    Integer(1152921504606846043),
    Integer(1152921504606847909),
    Integer(55),
    GF((4 * 2**61 * 3**56 * 19 - 1)**2, modulus=[1, 0, 1], names='i')
]

if __name__ == "__main__":
    generate_params(heuristic=True)
