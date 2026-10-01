from sage.all import Zmod, is_prime_power, matrix, randint

from vendors.Kummer_Isogeny.kummer_isogeny import KummerLineIsogeny
from vendors.Kummer_Isogeny.kummer_line import KummerLine, KummerPoint


def get_random_GL2(N):
    """Returns a random invertible 2x2 matrix over Z/NZ."""
    mat = matrix(Zmod(N), 2, 2, [randint(0, N - 1) for _ in range(4)])
    while not mat.det().is_unit():
        mat = matrix(Zmod(N), 2, 2, [randint(0, N - 1) for _ in range(4)])
    return mat


def x_only_linear_comb(xP, xQ, xPQ, a, b, order):
    """Computes x(a*P + b*Q) using KummerLine arithmetic."""
    Zmod_order = Zmod(order)
    a_mod = Zmod_order(a)
    b_mod = Zmod_order(b)
    if a_mod.is_unit():
        m = b_mod / a_mod
        x_PmQ = xQ.ladder_3_pt(xP, xPQ, m)  # P + m*Q
        return a * x_PmQ
    else:
        m = a_mod / b_mod
        x_QmP = xP.ladder_3_pt(xQ, xPQ, m)  # Q + m*P
        return b * x_QmP


def kummer_basis_from_points(kum, P, Q):
    """Returns (xP, xQ, xPQ) by lifting EC points P, Q into a KummerLine."""
    return kum(P), kum(Q), kum(P - Q)


def x_only_has_codomain(vector, kummer_basis, N, domain, codomain):
    """The kernel of an isogeny is given by the vector wrt the basis. returns true if the isogeny with this kernel has codomain `codomain`."""
    assert isinstance(domain, KummerLine) and isinstance(codomain, KummerLine)
    a, b = vector
    xP, xQ, xPQ = kummer_basis
    ker = x_only_linear_comb(xP, xQ, xPQ, a, b, N)
    phi = KummerLineIsogeny(domain, ker, N)
    return phi.codomain() == codomain

def x_only_has_codomain_and_mapping(
    vector, kummer_basis, N, domain, codomain, points, expected_images
):
    """The kernel of an isogeny is given by the vector wrt the basis. returns true if the isogeny with this kernel has codomain `codomain`."""
    assert isinstance(domain, KummerLine) and isinstance(codomain, KummerLine)
    assert all(isinstance(p, KummerPoint) for p in points)

    a, b = vector
    xP, xQ, xPQ = kummer_basis
    ker = x_only_linear_comb(xP, xQ, xPQ, a, b, N)
    phi = KummerLineIsogeny(domain, ker, N)
    if phi.codomain() != codomain:
        return False

    for xP, x_expected_image in zip(points, expected_images):
        if phi(xP) != x_expected_image:
            return False
    return True

def x_only_has_codomain_and_mapping_given_kernel(
    ker, N, domain, codomain, points, expected_images
):
    """The kernel of an isogeny is given by the vector wrt the basis. returns true if the isogeny with this kernel has codomain `codomain`."""
    assert isinstance(domain, KummerLine) and isinstance(codomain, KummerLine)
    assert all(isinstance(p, KummerPoint) for p in points)

    phi = KummerLineIsogeny(domain, ker, N)
    if phi.codomain() != codomain:
        return False

    for xP, x_expected_image in zip(points, expected_images):
        if phi(xP) != x_expected_image:
            return False
    return True


def x_only_is_basis_cube(xP, xQ, xPQ, N, E):
    """Checks if the points with these x-coordinates form a basis of E[N] where N is a prime power. Additionally checks that the xPQ is the x-coordinate of P-Q or P+Q."""

    if not is_prime_power(N):
        return False

    P = xP.curve_point()
    Q = xQ.curve_point()

    if P not in E or Q not in E:
        return False

    PpQ_x = (P + Q).x()
    PmQ_x = (P - Q).x()
    xPQ_x = xPQ.x()
    if PpQ_x != xPQ_x and PmQ_x != xPQ_x:
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


def random_kummer_basis(xP, xQ, xPQ, order):
    """Returns (xP', xQ', xPQ', mat) where the new basis is a random GL2 transform of (xP, xQ)."""
    mat = get_random_GL2(order)
    xP_new = x_only_linear_comb(xP, xQ, xPQ, mat[0, 0], mat[0, 1], order)
    xQ_new = x_only_linear_comb(xP, xQ, xPQ, mat[1, 0], mat[1, 1], order)
    xPQ_new = x_only_linear_comb(xP, xQ, xPQ, mat[0, 0] - mat[1, 0], mat[0, 1] - mat[1, 1], order)
    return xP_new, xQ_new, xPQ_new, mat


def x_only_push_pair(phi, P, Q):
    """Images of P and Q under an x-only isogeny, with consistent signs.

    Each lift is only defined up to sign; x(P - Q) fixes the relative sign, so
    the pair agrees with one of the isogenies +phi or -phi.
    """
    domain = phi.domain()
    xP = phi(domain(P))
    xQ = phi(domain(Q))
    xPQ = phi(domain(P - Q))
    P_img = xP.curve_point()
    Q_img = xQ.curve_point()

    if (P_img - Q_img).x() != xPQ.x():
        Q_img = -Q_img
    return P_img, Q_img


def is_supersingular_and_correct_characteristic_kummer(E_kum, p):
    """
    Faster alternative to is_supersingular_and_correct_characteristic.
    """
    if E_kum.base_ring().characteristic() != p:
        return False

    n = p + 1
    for _ in range(3):
        # random_point() samples a random x-coordinate and checks if x^3+Ax^2+x
        # is a square — faster than Sage's generic E.random_point()
        xP = E_kum.random_point()
        if xP.is_zero():
            continue
        # Two multiplications by (p+1) via the x-only Montgomery ladder
        xnP = n * xP
        if not (n * xnP).is_zero():
            return False
    return True
