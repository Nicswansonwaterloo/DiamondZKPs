from sage.all import vector

from helpers.theta_arithmetic import (
    UnsupportedProductError,
    hadamard,
    normalize,
    same_point,
    square,
)
from vendors.Theta_SageMath.theta_isogenies.isomorphism import SplittingIsomorphism
from vendors.Theta_SageMath.theta_structures.couple_point import CouplePoint
from vendors.Theta_SageMath.theta_structures.dimension_one import (
    montgomery_point_to_theta_point,
    theta_null_point_to_montgomery_curve,
    theta_point_to_montgomery_point,
)
from vendors.Theta_SageMath.theta_structures.dimension_two import ThetaStructure
from vendors.Theta_SageMath.theta_structures.split_structure import SplitThetaStructure


class ProductTheta:
    """Convert between an arbitrary product theta chart and signed couples."""

    def __init__(self, O):
        self.O = normalize(O)
        splitting = SplittingIsomorphism(ThetaStructure(self.O))
        self.N = splitting.N.change_ring(self.O[0].parent())
        self.Ninv = self.N.inverse()

        self.O1, self.O2 = self.split_factors(self.to_split(self.O))
        self.curves = tuple(
            theta_null_point_to_montgomery_curve(T) for T in (self.O1, self.O2)
        )
        self.zero = CouplePoint(*(E(0) for E in self.curves))

    @staticmethod
    def split_factors(P):
        """Recover (a:b), (c:d) from (ac:bc:ad:bd)."""
        x, y, z, t = P
        if not any(P) or x * t != y * z:
            raise ValueError("Point is not on this product theta surface")

        if x:
            return (x, y), (x, z)
        if z:
            return (z, t), (x, z)
        if y:
            return (x, y), (y, t)
        return (z, t), (y, t)

    def to_split(self, P):
        return tuple(self.N * vector(P))

    def split_coords(self, P):
        if not isinstance(P, CouplePoint) or P.curves() != self.curves:
            raise ValueError("Signed point belongs to a different elliptic product")

        a, b = montgomery_point_to_theta_point(self.O1, P[0])
        c, d = montgomery_point_to_theta_point(self.O2, P[1])
        return a * c, b * c, a * d, b * d

    def encode(self, P):
        split_coords = self.split_coords(P)
        return normalize(tuple(self.Ninv * vector(split_coords)))

    def lift(self, P):
        if isinstance(P, CouplePoint):
            if P.curves() != self.curves:
                raise ValueError("Signed point belongs to a different elliptic product")
            return P

        factors = self.split_factors(self.to_split(normalize(P)))
        points = []
        for E, O, T in zip(self.curves, (self.O1, self.O2), factors):
            X, Z = theta_point_to_montgomery_point(O, T)
            points.append(SplitThetaStructure.to_points(E, X, Z))

        return CouplePoint(*points)

    @staticmethod
    def signs(P):
        """Enumerate the independent component signs lost in product coordinates."""
        P1, P2 = P
        yield CouplePoint(P1, P2)
        yield CouplePoint(P1, -P2)
        yield CouplePoint(-P1, P2)
        yield CouplePoint(-P1, -P2)

    def kernel(self, triple):
        """Recover compatible generators using the supplied P+Q coordinate."""
        P, Q, S = triple
        if all(isinstance(T, CouplePoint) for T in triple):
            P, Q, S = map(self.lift, triple)
            sum_point = P + Q
            if S in (sum_point, -sum_point):
                return P, Q, sum_point
            difference = P - Q
            if S in (difference, -difference):
                return P, -Q, difference
            raise ValueError("Signed kernel sum is inconsistent with its generators")

        if any(isinstance(T, CouplePoint) for T in triple):
            raise ValueError("Use either three signed points or three theta coordinates")

        P, Q = self.lift(P), self.lift(Q)
        for candidate in self.signs(Q):
            sum_point = P + candidate
            if same_point(self.encode(sum_point), S):
                return P, candidate, sum_point

        raise ValueError("Product kernel sum is inconsistent with its generators")

    def recover_signs(self, P, translated, anchor):
        for candidate in self.signs(self.lift(P)):
            if same_point(self.encode(candidate + anchor), translated):
                return candidate

        raise ValueError(
            "Product image and reference translation have inconsistent signs"
        )

    def diff_add(self, A, P, Q, D):
        """Exceptional affine differential addition in a split product chart."""
        if A.Hinv is None:
            raise UnsupportedProductError(
                "Affine product addition needs a split theta chart"
            )

        P0, Q0 = self.lift(P), self.lift(Q)
        for candidate in self.signs(Q0):
            if same_point(self.encode(P0 - candidate), D):
                S = self.encode(P0 + candidate)
                break
        else:
            raise ValueError("Product differential-addition difference is inconsistent")

        U = hadamard(square(P))
        V = hadamard(square(Q))
        values = hadamard(tuple(u * v * h for u, v, h in zip(U, V, A.Hinv)))
        i = next((i for i in range(4) if D[i] and S[i]), None)
        if i is None:
            raise ValueError("Affine product addition has no common nonzero coordinate")

        # The addition identity gives D[i] * S[i], fixing the affine scale of S.
        scale = values[i] * A.inv4 / (D[i] * S[i])
        return tuple(scale * s for s in S)

