"""Quaternion routines ported from SQIsign2DSquare's Julia sources.

Original source:
https://github.com/Kaizhan-Lin/SQIsign2DSquare
commit 176634178cf8b42e7261eb383911ea5781a377d2

This file ports the small portion of ``order.jl``, ``cornacchia.jl``, and
``klpt.jl`` used by the full-degree ``RanIso`` construction.
"""

from dataclasses import dataclass

from sage.all import Integer, gcd, isqrt, randint


SmallPrimes = [
    2,
    3,
    5,
    7,
    11,
    13,
    17,
    19,
    23,
    29,
    31,
    37,
    41,
    43,
    47,
    53,
    59,
    61,
    67,
    71,
    73,
    79,
    83,
    89,
    97,
]


@dataclass(frozen=True)
class QOrderElem:
    """Element of ``<1, i, (i+j)/2, (1+ij)/2>`` in ``B_{p,infinity}``."""

    a: Integer
    b: Integer
    c: Integer
    d: Integer
    p: Integer

    def __post_init__(self):
        object.__setattr__(self, "a", Integer(self.a))
        object.__setattr__(self, "b", Integer(self.b))
        object.__setattr__(self, "c", Integer(self.c))
        object.__setattr__(self, "d", Integer(self.d))
        object.__setattr__(self, "p", Integer(self.p))

    def __getitem__(self, i):
        return (self.a, self.b, self.c, self.d)[i]

    def __add__(self, other):
        if isinstance(other, int) or isinstance(other, Integer):
            other = QOrderElem(other, 0, 0, 0, self.p)
        return QOrderElem(
            self.a + other.a,
            self.b + other.b,
            self.c + other.c,
            self.d + other.d,
            self.p,
        )

    def __rmul__(self, scalar):
        return QOrderElem(
            scalar * self.a,
            scalar * self.b,
            scalar * self.c,
            scalar * self.d,
            self.p,
        )

    def content(self):
        return gcd([self.a, self.b, self.c, self.d])

    def involution(self):
        return QOrderElem(self.a + self.d, -self.b, -self.c, -self.d, self.p)

    def norm(self):
        return (
            (2 * self.a + self.d) ** 2
            + (2 * self.b + self.c) ** 2
            + self.p * (self.c**2 + self.d**2)
        ) // 4


def Cornacchia_Smith(q):
    """Return ``a,b`` such that ``a^2+b^2=q`` for prime ``q=1 mod 4``."""

    # Sage's modular square root implements the same Tonelli-Shanks step used
    # by the Julia source's sqrt_mod helper.
    from sage.all import Mod

    if q == 2:
        return Integer(1), Integer(1)
    x = Integer(Mod(-1, q).sqrt())
    a = Integer(q)
    b = x
    c = isqrt(q)
    while b > c:
        a, b = b, a % b
    return b, isqrt(q - b**2)


def sum_of_two_squares(n):
    """Port of ``cornacchia.jl::sum_of_two_squares``."""

    n = Integer(n)
    if n <= 0:
        return Integer(0), Integer(0), False
    if n == 1:
        return Integer(1), Integer(0), True

    a, b = Integer(1), Integer(0)
    for ell in SmallPrimes:
        e = 0
        while n % ell == 0:
            n //= ell
            e += 1

        s = Integer(ell) ** (e // 2)
        a *= s
        b *= s
        if e % 2 == 1:
            if ell % 4 == 3:
                return Integer(0), Integer(0), False
            s, t = Cornacchia_Smith(Integer(ell))
            a, b = a * s - b * t, a * t + b * s

    if n % 4 == 1 and n.is_pseudoprime():
        s, t = Cornacchia_Smith(n)
        a, b = a * s - b * t, a * t + b * s
    elif n > 1:
        return Integer(0), Integer(0), False

    return a, b, True


def FullRepresentInteger(M, p, number_of_trials=16384):
    """Port of ``klpt.jl::FullRepresentInteger`` (Algorithm 10)."""

    M = Integer(M)
    p = Integer(p)
    counter = 0
    found = False
    x = y = z = w = Integer(0)

    while not found and counter < number_of_trials:
        m = isqrt((4 * M) // p)
        z = Integer(randint(-m, m))
        md = isqrt((4 * M - p * z**2) // p)
        w = Integer(randint(-md, md))
        Md = 4 * M - p * (z**2 + w**2)
        x, y, found = sum_of_two_squares(Md)
        if not found or (x - w) % 2 != 0 or (y - z) % 2 != 0:
            found = False
            counter += 1

    if found:
        alpha = QOrderElem((x - w) // 2, (y - z) // 2, z, w, p)
        assert alpha.norm() == M
        return alpha, found

    return QOrderElem(0, 0, 0, 0, p), found
