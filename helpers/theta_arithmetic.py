from functools import cached_property
from itertools import product

from sage.all import matrix
from sage.structure.element import get_coercion_model

from vendors.Theta_SageMath.theta_structures.dimension_two import ThetaStructure
from vendors.Theta_SageMath.utilities.batched_inversion import batched_inversion
from vendors.Theta_SageMath.utilities.fast_sqrt import sqrt_Fp2


def normalize(P):
    if len(P) != 4 or not any(P):
        raise ValueError("Theta coordinates must be a nonzero four-tuple")

    field = get_coercion_model().common_parent(*P)
    P = tuple(field(c) for c in P)

    for coordinate in P:
        if coordinate:
            inv = 1 / coordinate
            break

    return tuple(coordinate * inv for coordinate in P)


def same_point(P, Q):
    if not any(P) or not any(Q):
        return False

    for i in range(4):
        if Q[i]:
            break

    if not P[i]:
        return False

    for p, q in zip(P, Q):
        if p * Q[i] != q * P[i]:
            return False

    return True


def hadamard(P):
    x, y, z, t = P
    a = x + y
    b = x - y
    c = z + t
    d = z - t
    return a + c, b + d, a - c, b - d


def square(P):
    return tuple(c * c for c in P)


def multiply(P, Q):
    return tuple(p * q for p, q in zip(P, Q))


def coordinate_products(P):
    """Group coordinate products into the diagonal and three off-diagonal pairs."""
    a, b, c, d = P
    return (
        (a * a, b * b, c * c, d * d),
        (a * b, a * b, c * d, c * d),
        (a * c, b * d, a * c, b * d),
        (a * d, b * c, b * c, a * d),
    )


class UnsupportedProductError(ValueError):
    """A product operation needs elliptic-component signs that are unavailable."""


class ThetaArithmetic:
    def __init__(self, O):
        self.O = normalize(O)
        self.field = self.O[0].parent()
        self.one = self.field(1)
        self.zero = self.field(0)
        self.inv2 = self.one / self.field(2)
        self.inv4 = self.inv2 * self.inv2

        self.H = hadamard(square(self.O))
        self.Hinv = tuple(batched_inversion(*self.H)) if all(self.H) else None
        self.Oinv = tuple(batched_inversion(*self.O)) if all(self.O) else None

    @cached_property
    def is_product(self):
        # A product has a vanishing even theta constant.
        a, b, c, d = self.O
        a2 = a * a
        b2 = b * b
        c2 = c * c
        d2 = d * d

        even_theta_constants = (
            a2 + b2 + c2 + d2,
            a2 - b2 + c2 - d2,
            a2 + b2 - c2 - d2,
            a2 - b2 - c2 + d2,
            2 * (a * b + c * d),
            2 * (a * b - c * d),
            2 * (a * c + b * d),
            2 * (a * c - b * d),
            2 * (a * d + b * c),
            2 * (a * d - b * c),
        )
        return any(value == 0 for value in even_theta_constants)

    @cached_property
    def product_coordinates(self):
        from helpers.product_theta import ProductTheta

        return ProductTheta(self.O)

    @cached_property
    def biquadratic_coefficients(self):
        diagonal, ab_cd, ac_bd, ad_bc = (
            hadamard(row) for row in coordinate_products(self.O)
        )
        # Only the even entries contribute; the other entries vanish identically.
        return (
            tuple(self.one / value for value in diagonal),
            (self.one / ab_cd[0], None, self.one / ab_cd[2], None),
            (self.one / ac_bd[0], self.one / ac_bd[1], None, None),
            (self.one / ad_bc[0], None, None, self.one / ad_bc[3]),
        )

    def biquadratic(self, P, Q):
        """Return the symmetric matrix of biquadratic forms evaluated at P and Q."""
        rows = []
        for P_products, Q_products, coefficients in zip(
            coordinate_products(P), coordinate_products(Q), self.biquadratic_coefficients
        ):
            U = hadamard(P_products)
            V = hadamard(Q_products)
            values = [self.zero] * 4
            for i, coefficient in enumerate(coefficients):
                if coefficient is not None:
                    values[i] = U[i] * V[i] * coefficient
            C = hadamard(values)
            rows.append(tuple(value * self.inv2 for value in C))

        diagonal, ab_cd, ac_bd, ad_bc = rows
        B = matrix(self.field, 4)
        for i in range(4):
            B[i, i] = diagonal[i]
        B[0, 1] = B[1, 0] = ab_cd[0]
        B[2, 3] = B[3, 2] = ab_cd[2]
        B[0, 2] = B[2, 0] = ac_bd[0]
        B[1, 3] = B[3, 1] = ac_bd[1]
        B[0, 3] = B[3, 0] = ad_bc[0]
        B[1, 2] = B[2, 1] = ad_bc[1]
        return B

    def sums(self, P, Q):
        if self.is_product:
            raise UnsupportedProductError(
                "General theta addition on a product needs component signs"
            )

        P, Q = normalize(P), normalize(Q)
        if P == Q:
            return normalize(self.double(P)), self.O

        B = self.biquadratic(P, Q)

        i = next((i for i in range(4) if B[i, i]), None)
        if i is None:
            i, j = next((i, j) for i in range(4) for j in range(i + 1, 4) if B[i, j])
            return normalize(B.row(i)), normalize(B.row(j))

        j = next((j for j in range(4) if B[i, j] ** 2 != B[i, i] * B[j, j]), None)
        if j is None:
            T = normalize(B.row(i))
            return T, T

        a, b, c = B[i, i] / 2, B[i, j], B[j, j] / 2
        discriminant = b * b - 4 * a * c
        if self.field.characteristic() % 4 == 3:
            root = sqrt_Fp2(discriminant)
        else:
            root = discriminant.sqrt(extend=False)
        if root * root != discriminant:
            raise ValueError("Theta addition roots are not defined over the base field")

        d = (b + root) / (2 * a)
        s = b - a * d
        D = tuple((B[k, j] - B[k, i] * d) / (s - a * d) for k in range(4))
        S = tuple(B[k, i] - a * D[k] for k in range(4))

        return normalize(S), normalize(D)

    def _diff_add_with_inverses(self, P, Q, Dinv):
        """Compute P+Q using coordinate inverses of P-Q and nonzero self.H."""
        U = hadamard(square(P))
        V = hadamard(square(Q))
        products = multiply(U, V)
        scaled_products = multiply(products, self.Hinv)
        values = hadamard(scaled_products)
        sum_coordinates = multiply(values, Dinv)
        return tuple(coordinate * self.inv4 for coordinate in sum_coordinates)

    def diff_add(self, P, Q, D):
        """Compute P+Q from P, Q, and their known difference D = P-Q."""
        # The fast formula divides by every coordinate of D and self.H.
        if all(D) and self.Hinv is not None:
            Dinv = tuple(self.one / coordinate for coordinate in D)
            return self._diff_add_with_inverses(P, Q, Dinv)

        if self.is_product:
            return self.product_coordinates.diff_add(self, P, Q, D)

        B = self.biquadratic(P, Q)
        i = next(i for i in range(4) if D[i])

        # Recover S = P+Q from B[i,j] = S[i]*D[j] + S[j]*D[i].
        sum_coordinate = B[i, i] / (2 * D[i])
        S = []
        for j in range(4):
            if i == j:
                S.append(sum_coordinate)
            else:
                numerator = B[i, j] - sum_coordinate * D[j]
                S.append(numerator / D[i])
        return tuple(S)

    def double(self, P):
        """Compute 2P, using the origin as the known difference P-P."""
        if self.Oinv is not None and self.Hinv is not None:
            return self._diff_add_with_inverses(P, P, self.Oinv)

        if self.is_product:
            return self.mul(2, P)
        return self.diff_add(P, P, self.O)

    @cached_property
    def structure(self):
        return ThetaStructure(self.O)

    def triple(self, P):
        # [3]P = [2]P + P
        if all(P) and self.Hinv is not None and self.Oinv is not None:
            T = self.structure(P)
            return T.double().diff_addition(T, T).coords()

        return normalize(self.diff_add(self.double(P), P, P))

    def triple_iter(self, P, n):
        for _ in range(n):
            P = self.triple(P)

        return P

    def mul(self, n, P):
        n = abs(int(n))
        P = normalize(P)

        if self.is_product:
            product = self.product_coordinates
            return product.encode(n * product.lift(P))

        if n == 0:
            return self.O
        if n == 1:
            return P

        if n <= 5:
            P2 = self.double(P)
            if n == 2:
                return normalize(P2)
            if n == 4:
                return normalize(self.double(P2))
            P3 = self.diff_add(P2, P, P)
            if n == 3:
                return normalize(P3)
            return normalize(self.diff_add(P3, P2, P))

        U, V = self.O, P
        Dinv = None
        if all(P) and self.Hinv is not None:
            Dinv = tuple(self.one / c for c in P)

        for bit in bin(n)[2:]:
            if Dinv is not None:
                S = self._diff_add_with_inverses(U, V, Dinv)
            else:
                S = self.diff_add(U, V, P)

            if bit == "0":
                U, V = self.double(U), S
            else:
                U, V = S, self.double(V)

        return normalize(U)

    def mul_add(self, n, P, Q, PQ):
        """Compute [n]P+Q, using the supplied P+Q to fix relative signs."""
        n = int(n)
        if n < 0:
            raise ValueError("mul_add expects a nonnegative scalar")

        if n == 0:
            return Q
        if n == 1:
            return PQ

        X, Y, Z = P, PQ, Q
        scalar = n - 1

        while scalar > 1:
            dX = self.double(X)
            if scalar % 2:
                Y = self.diff_add(X, Y, Z)
            else:
                Z = self.diff_add(X, Z, Y)
            X = dX
            scalar //= 2

        return self.diff_add(X, Y, Z)

    def extended_add(self, X, Y, Z, XY, YZ, ZX):
        """Three-way addition from the three pairwise sums (Riemann relation)."""
        U = hadamard(multiply(self.O, YZ))
        V = hadamard(multiply(ZX, XY))
        W = hadamard(multiply(Y, Z))

        if all(X) and all(W):
            H = hadamard(tuple(u * v / w for u, v, w in zip(U, V, W)))
            return tuple(h / (4 * x) for h, x in zip(H, X))

        # Recover the sign from the same pairwise sums in exceptional charts.
        candidates = set(self.sums(XY, Z))
        candidates.intersection_update(self.sums(X, YZ))
        candidates.intersection_update(self.sums(Y, ZX))
        if len(candidates) != 1:
            raise ValueError("Pairwise sums do not determine a unique three-way sum")

        return candidates.pop()

    def theta_changes(self):
        # Small, deterministic set of changes sufficient for ordinary chart
        # failures. Unsupported exceptional charts raise explicitly.
        z = self.field.gen()
        if z * z != -1:
            z = self.field(-1).sqrt(extend=False)

        # The four phase patterns for the two binary coordinate indices.
        phases = ((1, 1, 1, 1), (1, z, 1, z), (1, 1, z, z), (1, z, z, 1))
        for use_hadamard, perm, phase in product(
            (False, True), ((0, 1, 2, 3), (0, 2, 1, 3)), phases
        ):

            def change(P, use_hadamard=use_hadamard, perm=perm, phase=phase):
                Q = multiply(P, phase)
                if use_hadamard:
                    Q = hadamard(Q)
                return tuple(Q[j] for j in perm)

            yield change
