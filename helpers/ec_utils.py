from sage.all import GF, Zmod, discrete_log, gcd, is_prime_power, matrix, randint, vector
from sage.schemes.elliptic_curves.ell_finite_field import special_supersingular_curve

from vendors.Theta_SageMath.utilities.supersingular import generate_point_order_D


def find_independent_point(E, P, order):
    """Returns a random point Q of given order on E such that (P, Q) is a basis for E[order]. where order = 5^e5"""
    gen = generate_point_order_D(E, order)
    Q = next(gen)
    while Q.weil_pairing(P, order) ** (order // 5) == 1:
        Q = next(gen)
    return Q


def random_supersingular_curve(p):
    F = GF(p**2, modulus=[1, 0, 1], names="i")
    E = special_supersingular_curve(F)  # always returns a model with (p + 1)^2 points
    K = E.random_point()
    E_rand = E.isogeny(K, algorithm="factored", model="montgomery").codomain()
    return E_rand


def get_coefficients_wrt(P, Q, R, ell):
    """
    Returns a, b such that R = [a]P + [b]Q in E[ell].
    Requires dlog mod ell.
    """
    w_PQ = P.weil_pairing(Q, ell)
    w_RQ = R.weil_pairing(Q, ell)
    a = discrete_log(w_RQ, w_PQ, ord=ell)
    w_QP = 1 / w_PQ
    w_RP = R.weil_pairing(P, ell)
    b = discrete_log(w_RP, w_QP, ord=ell)
    assert R == a * P + b * Q
    return a, b


def randomize_basis(torsion_basis, N, sk_vector=None):
    """
    Given a fixed basis for the N-torsion, returns a random basis by sampling a
    random element of GL_2(Z/NZ) and applying it to the fixed basis.
    Optionally converts a secret key vector to the random basis as well.
    """
    change_of_basis = matrix(Zmod(N), 2, 2, [randint(0, N - 1) for _ in range(4)])
    while not change_of_basis.det().is_unit():
        change_of_basis = matrix(Zmod(N), 2, 2, [randint(0, N - 1) for _ in range(4)])

    random_basis = [
        change_of_basis[0, 0] * torsion_basis[0] + change_of_basis[0, 1] * torsion_basis[1],
        change_of_basis[1, 0] * torsion_basis[0] + change_of_basis[1, 1] * torsion_basis[1],
    ]

    if sk_vector is not None:
        sk_in_random_basis = vector(Zmod(N), sk_vector) * change_of_basis.inverse()
        return random_basis, change_of_basis, sk_in_random_basis
    else:
        return random_basis, change_of_basis


def is_supersingular_and_correct_characteristic(E, p):
    return E.is_supersingular(proof=False) and E.base_ring().characteristic() == p


def is_basis_cube(P, Q, N, E):
    if P not in E or Q not in E:
        return False
    if not is_prime_power(N):
        return False

    e = P.weil_pairing(Q, N)
    if e**N != 1:
        return False

    if N % 2 == 0:
        return e ** (N // 2) != 1
    if N % 3 == 0:
        return e ** (N // 3) != 1
    if N % 5 == 0:
        return e ** (N // 5) != 1
    return False


def is_basis_windmill(P, Q, N, ells, E):
    "Checks if P, Q form a basis for E[N] with N = prod(ells)"
    if P not in E or Q not in E:
        return False

    e = P.weil_pairing(Q, N)

    if e**N != 1:
        return False

    for ell in ells:
        if e ** (N // ell) == 1:
            return False

    return True


def has_codomain(vector, basis, N, domain, codomain):
    if gcd(gcd(vector[0], vector[1]), N) != 1:
        return False
    kernel = vector[0] * basis[0] + vector[1] * basis[1]
    phi = domain.isogeny(kernel, algorithm="factored", codomain=codomain)
    return phi.codomain().j_invariant() == codomain.j_invariant()


def has_codomain_and_mapping(vector, basis, N, domain, codomain, points, point_images):
    if gcd(gcd(vector[0], vector[1]), N) != 1:
        return False

    kernel = vector[0] * basis[0] + vector[1] * basis[1]
    phi = domain.isogeny(kernel, algorithm="factored", codomain=codomain)
    if phi.codomain().j_invariant() != codomain.j_invariant():
        return False

    # Check that the mapping is correct on a basis that is coprime to the kernel
    for point, point_image in zip(points, point_images):
        if phi(point) != point_image and -phi(point) != point_image:
            return False

    return True
