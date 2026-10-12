"""Checks of the dimension-2 isogeny backend against elliptic-curve computations.

Run from the repository root: PYTHONPATH=. python tests/two_dim_isogeny_checks.py
"""

from itertools import combinations, permutations, product
from sage.all import EllipticCurve, GF, HyperellipticCurve, PolynomialRing, ZZ, Zmod, matrix, prod, set_random_seed

from helpers.product_theta import ProductTheta
from helpers.theta_arithmetic import ThetaArithmetic, normalize
from helpers.three_isogeny import ThreeIsogenyChain
from helpers.two_dim_utils import is_basis_theta, theta_matrix_basis_to_pts
from vendors.Theta_SageMath.theta_isogenies.gluing_isogeny import GluingThetaIsogeny
from vendors.Theta_SageMath.theta_isogenies.product_isogeny import EllipticProductIsogeny
from vendors.Theta_SageMath.theta_structures.couple_point import CouplePoint
from vendors.Theta_SageMath.theta_structures.dimension_one import montgomery_curve_to_theta_null_point
from vendors.Theta_SageMath.theta_structures.dimension_two import ThetaStructure

set_random_seed(20261012)
p = ZZ(3273941099519)
assert p.is_prime() and (p + 1) % (2**10 * 3**10 * 5 * 7 * 13 * 17) == 0
k = GF(p**2, modulus=[1, 0, 1], names="i")
i = k.gen()
E1728 = EllipticCurve(k, [1, 0])
E0 = EllipticCurve(k, [0, 133765064309, 0, 1, 0])
E8000 = EllipticCurve(j=k(8000)).montgomery_model()
assert E0.j_invariant() == 0
for E in (E1728, E0, E8000):
    E.set_order((p + 1)**2)
E5 = E1728.isogeny(E1728.torsion_basis(5)[0], model="montgomery").codomain()
E5.set_order((p + 1)**2)
assert E5.j_invariant() not in (0, 1728)


def chart(E, F):
    # Product theta null point of E x F, and the isomorphism onto its curves.
    a, b = montgomery_curve_to_theta_null_point(E)
    c, d = montgomery_curve_to_theta_null_point(F)
    Th = ProductTheta((a * c, b * c, a * d, b * d))
    f, g = E.isomorphism_to(Th.curves[0]), F.isomorphism_to(Th.curves[1])
    return Th, lambda T: CouplePoint(f(T[0]), g(T[1]))


def sample(E, F):
    P, Q = E.torsion_basis(5)
    R, S = F.torsion_basis(5)
    return ([CouplePoint(E(0), F(0)), CouplePoint(P, F(0)), CouplePoint(E(0), R)]
            + [CouplePoint(P + a * Q, R + (a + 1) * S) for a in range(3)]
            + [CouplePoint(E.random_point(), F.random_point()) for _ in range(4)])


def assert_product_map(source, target, expected, actual):
    # Some fixed isomorphism source -> target matches all images up to component signs.
    for s in permutations((0, 1)):
        for f, g in product(source[s[0]].isomorphisms(target[0]), source[s[1]].isomorphisms(target[1])):
            if all(Y[0] in (f(X[s[0]]), -f(X[s[0]])) and Y[1] in (g(X[s[1]]), -g(X[s[1]]))
                   for X, Y in zip(expected, actual)):
                return
    raise AssertionError("no product isomorphism matches the images")


def cyclic(E, d):
    return E.isogeny(E.torsion_basis(d)[0], algorithm="factored", model="montgomery")


def kani(h, r=1, m=None):
    # Phi = (1 + J)^r = a + bJ on E x F, J = [[0, -h^], [h, 0]], q = 1 + deg h, J^2 = 1 - q.
    E, F, hd, q = h.domain(), h.codomain(), h.dual(), h.degree() + 1
    F.set_order(E.order())
    a, b = ZZ(1), ZZ(0)
    for _ in range(r):
        a, b = a - (q - 1) * b, a + b
    n = q**r
    assert a**2 + (q - 1) * b**2 == n
    Phi = lambda T: CouplePoint(a * T[0] - b * hd(T[1]), b * h(T[0]) + a * T[1])
    Phi_dual = lambda T: CouplePoint(a * T[0] + b * hd(T[1]), -b * h(T[0]) + a * T[1])
    # ker Phi = {(b h^(T), a T) : T in F[n]}; m = 4n gives the points above it.
    K = [CouplePoint(b * hd(T), a * T) for T in F.torsion_basis(m or n)]
    for T in sample(E, F):
        assert Phi_dual(Phi(T)) == n * T
    return F, n, Phi, K


print("Product theta arithmetic", flush=True)
Th, _ = chart(E1728, E1728)
A = ThetaArithmetic(Th.O)
E, F = Th.curves
assert A.is_product and Th.encode(Th.zero) == A.O and Th.lift(A.O) == Th.zero
points = sample(E, F)
for P in points:
    X = Th.encode(P)
    assert Th.encode(Th.lift(X)) == X
    assert all(Th.encode(Q) == X for Q in Th.signs(P))
    for n in (-9, -1, 0, 1, 2, 3, 5, 17, 27):
        assert normalize(A.mul(n, X)) == Th.encode(n * P)
    assert normalize(A.double(X)) == Th.encode(2 * P)
    assert normalize(A.triple(X)) == Th.encode(3 * P)
for P, Q in zip(points, reversed(points)):
    X, Y, D, S = [Th.encode(T) for T in (P, Q, P - Q, P + Q)]
    assert normalize(A.diff_add(X, Y, D)) == S
    for n in (0, 1, 2, 7):
        assert normalize(A.mul_add(n, X, Y, S)) == Th.encode(n * P + Q)

# 4-torsion with a vanishing theta coordinate.
P, Q = E.torsion_basis(4)
R, S = F.torsion_basis(4)
U = CouplePoint(P, R)
for a, b, c, d in product(range(4), repeat=4):
    T = CouplePoint(a * P + b * Q, c * R + d * S)
    X = Th.encode(T)
    if all(X):
        continue
    assert normalize(A.double(X)) == Th.encode(2 * T)
    assert normalize(A.triple(X)) == Th.encode(3 * T)
    assert normalize(A.diff_add(Th.encode(T + U), Th.encode(U), X)) == Th.encode(T + 2 * U)

# Every symplectic change of chart keeps a product structure on E x F.
for change in A.theta_changes():
    B = ThetaArithmetic(change(A.O))
    target = ProductTheta(B.O)
    assert B.is_product
    assert_product_map((E, F), target.curves, points, [target.lift(change(Th.encode(P))) for P in points])
    for P in points:
        X = change(Th.encode(P))
        for n in (0, 2, 7):
            assert normalize(B.mul(n, X)) == normalize(change(Th.encode(n * P)))
        assert normalize(B.double(X)) == normalize(change(Th.encode(2 * P)))
        assert normalize(B.triple(X)) == normalize(change(Th.encode(3 * P)))

# P + Q and P - Q nonzero on disjoint coordinates: the affine scale needs another Riemann relation.
T = E.lift_x(k(1))
V = next(R for R in E.torsion_basis(4) if 2 * R != 2 * T)
Q = CouplePoint(V, F(0))
P = CouplePoint(T, F(0)) + Q
X, Y, D, S = [Th.encode(T) for T in (P, Q, P - Q, P + Q)]
assert not any(d * s for d, s in zip(D, S))
assert normalize(A.diff_add(X, Y, D)) == S
a, b, c = k(3), i, k(7)
Z = A.diff_add(X, Y, D)
assert A.diff_add(tuple(a * x for x in X), tuple(b * y for y in Y), tuple(c * d for d in D)) == tuple(a**2 * b**2 / c * z for z in Z)

P, Q = E.torsion_basis(5)
R, S = F.torsion_basis(5)
U = CouplePoint(P, R)
for a, b in product(range(5), repeat=2):
    T = CouplePoint(a * Q, b * S)
    assert Th.recover_signs(Th.encode(T), Th.encode(T + U), U) == T

print("Odd isogenies: identity, diagonal quotients, the 40 isotropic 3-kernels", flush=True)
phi = ThreeIsogenyChain.from_degree(Th.O, (), 1)
assert phi.codomain.O == Th.O
assert all(phi(P) == Th.encode(P) == phi(Th.encode(P)) for P in sample(E, F))

for n in (3, 9, 27):
    P, Q = E.torsion_basis(n)[0], F.torsion_basis(n)[0]
    K, L = CouplePoint(P, F(0)), CouplePoint(E(0), Q)
    phi = ThreeIsogenyChain.from_degree(Th.O, (K, L), n)
    f, g = E.isogeny(P, algorithm="factored"), F.isogeny(Q, algorithm="factored")
    assert all(step.codomain.is_product for step in phi._maps)
    target = ProductTheta(phi.codomain.O)
    points = sample(E, F)
    assert_product_map((f.codomain(), g.codomain()), target.curves,
                       [CouplePoint(f(T[0]), g(T[1])) for T in points], [target.lift(phi(T)) for T in points])
    assert all(phi(a * K + b * L) == phi.codomain.O for a, b in product(range(n), repeat=2))
    for step in phi._maps[:-1]:
        assert all(step(P + Q) == step(P) + step(Q) for P, Q in zip(points, reversed(points)))
        points = [step(P) for P in points]
    if n == 9:
        # Other generators of the same kernel give the same isogeny.
        points = sample(E, F)
        images = [target.lift(phi(T)) for T in points]
        for U, V in ((L, K), (-K, L), (K + L, K + 2 * L)):
            psi = ThreeIsogenyChain.from_degree(Th.O, (U, V), 9)
            B = ProductTheta(psi.codomain.O)
            assert_product_map(target.curves, B.curves, images, [B.lift(psi(T)) for T in points])
    if n == 3:
        # A kernel given by scaled theta coordinates of K, L, K + L.
        triple = [[c * x for x in Th.encode(T)] for c, T in zip((k(2), i, k(7)), (K, L, K + L))]
        psi = ThreeIsogenyChain.from_degree(Th.O, triple, 3)
        assert all(psi(T) == phi(T) for T in sample(E, F))

# Kani: a non-diagonal 3-kernel has product quotient iff it is the graph of a 2-isogeny on E[3].
P, Q = E.torsion_basis(3)
R, S = F.torsion_basis(3)
S = S if P.weil_pairing(Q, 3) == R.weil_pairing(S, 3) else -S  # symplectic basis of E[3] x F[3]
pt = {v: CouplePoint(v[0] * P + v[1] * Q, v[2] * R + v[3] * S) for v in product(range(3), repeat=4)}
graphs = {frozenset((a * P + b * Q, u(h(a * P + b * Q))) for a, b in product(range(3), repeat=2))
          for h in E.isogenies_prime_degree(2) for u in h.codomain().isomorphisms(F)}
kernels = {}
for u, v in combinations(list(pt)[1:], 2):
    if (u[0] * v[1] - u[1] * v[0] + u[2] * v[3] - u[3] * v[2]) % 3 == 0:
        span = frozenset(tuple((a * x + b * y) % 3 for x, y in zip(u, v)) for a, b in product(range(3), repeat=2))
        if len(span) == 9:
            kernels.setdefault(span, (u, v))
assert len(kernels) == 40
diagonal = 0
for span, (u, v) in kernels.items():
    K, L = pt[u], pt[v]
    diagonal += K[0].weil_pairing(L[0], 3) == 1
    phi = ThreeIsogenyChain.from_degree(Th.O, (K, L), 3)
    split = K[0].weil_pairing(L[0], 3) == 1 or frozenset((pt[w][0], pt[w][1]) for w in span) in graphs
    assert phi.codomain.is_product == split
    assert all((phi(T) == phi.codomain.O) == (w in span) for w, T in pt.items())
assert diagonal == 16

print("Odd Kani chains (1 + J)^r", flush=True)
for E in (E1728, E0, E5):
    for q, r in ((3, 6), (9, 3)):
        h = cyclic(E, q - 1)
        F, n, Phi, (K, L) = kani(h, r)
        assert K.weil_pairing(L, n) == 1 and K[1].weil_pairing(L[1], n).multiplicative_order() == n
        Th, iota = chart(E, F)
        phi = ThreeIsogenyChain.from_degree(Th.O, (iota(K), iota(L)), n)
        points = sample(E, F)
        images = [iota(T) for T in points]
        # q = 3 is a product after every step, q = 9 after every second step.
        s = 1 if q == 3 else 2
        assert len(phi._maps) == s * r
        for j, step in enumerate(phi._maps, 1):
            images = [step(T) for T in images]
            assert step.codomain.is_product == (j % s == 0)
            if j % s == 0:
                target = ProductTheta(step.codomain.O)
                Phi_j = kani(h, j // s)[2]
                assert_product_map((E, F), target.curves, [Phi_j(T) for T in points], [target.lift(T) for T in images])
        for T in points:
            assert phi(iota(T + K)) == phi(iota(T + L)) == phi(iota(T))
        P, R = E.torsion_basis(5)[0], F.torsion_basis(5)[0]
        for T in (CouplePoint(P, F(0)), CouplePoint(E(0), R)):
            X = phi(iota(T))
            assert X != phi.codomain.O and phi.codomain.mul(5, X) == phi.codomain.O

print("Even Kani chains and Jacobian arithmetic", flush=True)
for E, n in ((E1728, 8), (E1728, 16), (E0, 64), (E5, 64), (E1728, 256)):
    F, n, Phi, K = kani(cyclic(E, n - 1), m=4 * n)
    phi = EllipticProductIsogeny.from_degree(K, n)
    points = sample(E, F)
    assert_product_map((E, F), phi.codomain(), [Phi(T) for T in points], [phi(T) for T in points])
    O = CouplePoint(*(C(0) for C in phi.codomain()))
    assert phi(points[0]) == O
    assert all(phi(4 * a * K[0] + 4 * b * K[1]) == O for a, b in product(range(0, n, n // 8), repeat=2))

E = E1728
F, _, _, K = kani(cyclic(E, 7), m=32)
phi = EllipticProductIsogeny.from_degree(K, 8, split=False)
A = ThetaArithmetic(phi.codomain().coords())
assert A.is_product
for T in sample(E, F):
    X = normalize(phi(T).coords())
    assert normalize(phi(-T).coords()) == X
    assert all(normalize(phi(T + 4 * R).coords()) == X for R in (K[0], K[1], K[0] + K[1]))

theta = lambda T: normalize(phi._phis[0](T).coords())
A = ThetaArithmetic(phi._phis[0].codomain().coords())
assert not A.is_product and theta(CouplePoint(E(0), F(0))) == A.O
points = sample(E, F)
for P in points:
    assert all(A.mul(n, theta(P)) == theta(n * P) for n in (-5, 0, 1, 2, 3, 4, 16, 27))
    X = phi._phis[0](P)
    assert all(normalize(X.double_iter(r).coords()) == theta(2**r * P) for r in range(4))
for P, Q in zip(points, reversed(points)):
    X, Y, S = theta(P), theta(Q), theta(P + Q)
    assert set(A.sums(X, Y)) == {S, theta(P - Q)}
    assert normalize(A.diff_add(X, Y, theta(P - Q))) == S
    assert all(normalize(A.mul_add(n, X, Y, S)) == theta(n * P + Q) for n in (0, 1, 2, 7))
for P, Q, R in zip(points[3:], points[4:], points[5:]):
    assert normalize(A.extended_add(*[theta(T) for T in (P, Q, R, P + Q, Q + R, R + P)])) == theta(P + Q + R)

# Images of E[3] x F[3] are the 41 classes modulo simultaneous sign; 4 points of E[2] x F[2] die.
P, Q = E.torsion_basis(3)
R, S = F.torsion_basis(3)
images = {theta(CouplePoint(a * P + b * Q, c * R + d * S)) for a, b, c, d in product(range(3), repeat=4)}
assert len(images) == 41 and all(A.mul(3, X) == A.O for X in images)
P, Q = E.torsion_basis(2)
R, S = F.torsion_basis(2)
torsion = [CouplePoint(a * P + b * Q, c * R + d * S) for a, b, c, d in product(range(2), repeat=4)]
killed = [T for T in torsion if theta(T) == A.O]
assert len(killed) == 4
assert sum(T[0].is_zero() for T in killed) == sum(T[1].is_zero() for T in killed) == 1

# Kernel bases from a matrix over Z/9 in the theta basis used by the protocol.
P, Q = E.torsion_basis(9)
R, S = F.torsion_basis(9)
B = [CouplePoint(P, F(0)), CouplePoint(Q, F(0)), CouplePoint(E(0), R), CouplePoint(E(0), S)]
theta_B = [phi._phis[0](T) for T in B]
assert is_basis_theta(theta_B, 9, phi._phis[0].codomain())
assert not is_basis_theta(theta_B[:3] + theta_B[:1], 9, phi._phis[0].codomain())
sums = [theta(B[a] + B[b]) for a, b in combinations(range(4), 2)]
for rows in ([[1, 2, 3, 4], [0, 1, 2, 5]], [[3, 1, 0, 2], [1, 0, 4, 5]]):
    M = matrix(Zmod(9), rows)
    U, V = theta_matrix_basis_to_pts(M, [T.coords() for T in theta_B], sums, A.O, 9)
    G = [sum((ZZ(c) * T for c, T in zip(row, B)), CouplePoint(E(0), F(0))) for row in M]
    span = {theta(a * G[0] + b * G[1]) for a, b in product(range(9), repeat=2)}
    assert len(span) == 41 and U in span and V in span
    assert A.O not in (A.mul(3, U), A.mul(3, V)) and A.mul(3, U) != A.mul(3, V)

print("Gluing codomains against the Florit--Smith sextic", flush=True)


def gluing_sextic(s, t):
    # Florit--Smith, An atlas of the Richelot isogeny graph, Section 2.2 (arXiv:2101.00917).
    c = ((0, 1, 2), (1, 2, 0), (2, 0, 1))
    a1 = sum((s[j] - s[i])**2 / (t[j] - t[i]) for i, j, _ in c)
    a2 = sum(s[i] * (t[k] - t[j]) for i, j, k in c)
    b1 = sum((t[j] - t[i])**2 / (s[j] - s[i]) for i, j, _ in c)
    b2 = sum(t[i] * (s[k] - s[j]) for i, j, k in c)
    A = a1 / a2 * prod((t[i] - t[j])**2 for i, j, _ in c)
    B = b1 / b2 * prod((s[i] - s[j])**2 for i, j, _ in c)
    x = PolynomialRing(s[0].parent(), "x").gen()
    return -prod(A * (s[j] - s[i]) * (s[i] - s[k]) * x**2 + B * (t[j] - t[i]) * (t[i] - t[k]) for i, j, k in c)


jacobians = 0
for E, F in ((E0, E1728), (E1728, E1728), (E0, E0), (E8000, E8000)):
    P, Q = E.torsion_basis(8)
    R, S = F.torsion_basis(8)
    for U, V, _ in permutations((R, S, R + S)):
        if any(f(4 * P) == 4 * U and f(4 * Q) == 4 * V for f in E.isomorphisms(F)):
            continue  # the gluing kernel is the graph of an isomorphism: a product, not a Jacobian
        phi = GluingThetaIsogeny(CouplePoint(P, U), CouplePoint(Q, V))
        A = ThetaArithmetic(phi.codomain().coords())
        assert not A.is_product
        f = gluing_sextic([(4 * T)[0] for T in (P, Q, P + Q)], [(4 * T)[0] for T in (U, V, U + V)])
        I = HyperellipticCurve(f).igusa_clebsch_invariants()
        # Rosenhain's formulas divide by theta constants, so read the curve off a chart where they work.
        for change in A.theta_changes():
            try:
                J = ThetaStructure(change(A.O)).hyperelliptic_from_theta().igusa_clebsch_invariants()
                break
            except ValueError:
                pass
        else:
            raise AssertionError("no chart gives Rosenhain invariants")
        # Equal in weighted projective space P(2, 4, 6, 10).
        w = (2, 4, 6, 10)
        assert all(I[a]**w[b] * J[b]**w[a] == J[a]**w[b] * I[b]**w[a] for a, b in combinations(range(4), 2))
        jacobians += 1
assert jacobians == 18

print("Kani proof of concept, all three challenges", flush=True)
import kani_proof_of_concept as kani_poc

sk, pk = kani_poc.one_dim_key_gen()
commitment, responses = kani_poc.prover(sk, pk)
for c in range(3):
    assert kani_poc.verifier(pk, c, responses[c], commitment)
    assert not kani_poc.verifier(pk, c, responses[c], tuple("tampered" for _ in commitment))
print("All checks passed.")
