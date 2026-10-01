from sage.all import ZZ, cached_function, matrix

from helpers.product_theta import ProductTheta
from helpers.theta_arithmetic import ThetaArithmetic, UnsupportedProductError, normalize
from vendors.Theta_SageMath.theta_structures.couple_point import CouplePoint


class ThetaThreeIsogeny:
    """Quotient by an isotropic kernel (P,Q,P+Q) of order 3 squared.

    Coordinates are four-tuples. Product evaluations use signed CouplePoints;
    bare coordinates suffice only when the kernel is diagonal. Calling
    set_sign_reference enables signed output for an intermediate product.
    """

    def __init__(self, A, kernel, perform_checks=True):
        self.domain = A
        self.domain_product = None
        self.codomain_product = None

        if A.is_product:
            self.domain_product = ProductTheta(A.O)
            P, Q, S = self.domain_product.kernel(kernel)

            if any(
                3 * T != self.domain_product.zero or T == self.domain_product.zero
                for T in (P, Q)
            ):
                raise ValueError("Kernel generators must have order 3")
            if Q in (P, -P):
                raise ValueError("Kernel generators must be independent")
            if P.weil_pairing(Q, 3) != 1:
                raise ValueError("Isogeny kernel is not isotropic")

            self.diagonal = P[0].weil_pairing(Q[0], 3) == 1
            self.signed_generators = (Q, P, S, P - Q)
            self.change = self.domain_product.to_split
            self.source = ThetaArithmetic(self.change(A.O))
            kernel_coords = tuple(self.domain_product.split_coords(T) for T in (P, Q, S))
            O = self._compute(kernel_coords)
            self.codomain = ThetaArithmetic(O)
            return

        P, Q, S = map(normalize, kernel)

        if perform_checks:
            if any(A.mul(3, T) != A.O or T == A.O for T in (P, Q)):
                raise ValueError("Kernel generators must have order 3")
            if S not in A.sums(P, Q):
                raise ValueError("Third kernel point must represent P+Q or P-Q")

        for change in A.theta_changes():
            self.change = change
            self.source = ThetaArithmetic(change(A.O))
            try:
                O = self._compute(tuple(change(T) for T in (P, Q, S)))
            except ZeroDivisionError:
                continue

            if any(O):
                self.cubic = self._cubic_coefficients(O)
                if self.cubic is not None:
                    self.codomain = ThetaArithmetic(O)
                    return

        raise ValueError("Isogeny target vanishes in all supported theta charts")

    def _cubic_coefficients(self, O):
        """Fix the cubic map by requiring the origin and kernel to map to O.

        An odd-degree isogeny commutes with the level-2 theta group, so each
        image coordinate is the same combination of the five equivariant cubic
        forms. Evaluating that map needs no theta additions or square roots.
        """
        i = next(i for i in range(4) if O[i])
        rows = []
        for X in (self.source.O, *self.generators):
            forms = _cubic_forms(X)
            for j in range(4):
                if j != i:
                    rows.append([O[i] * f[j] - O[j] * f[i] for f in forms])

        kernel = matrix(self.source.field, rows).right_kernel_matrix()
        if kernel.nrows() != 1:
            return None
        return tuple(kernel[0])

    @staticmethod
    def _scale(P, Q):
        """Return c with P=cQ, checking every coordinate."""
        i = next(i for i in range(4) if Q[i])
        c = P[i] / Q[i]
        if not c or tuple(P) != tuple(c * q for q in Q):
            raise ValueError("Inconsistent affine differential-addition cycle")

        return c

    def _cycle(self, P, R, S):
        T = self.source.diff_add(S, R, P)
        return self._scale(self.source.diff_add(T, R, S), P)

    def _compute(self, kernel):
        A = self.source

        P, Q, S = map(normalize, kernel)

        # Four representatives of the nonzero kernel modulo overall sign.
        self.generators = Q, P, S, normalize(A.diff_add(S, Q, P))
        if self.domain_product is None and len({A.O, *self.generators}) != 5:
            raise ValueError("Kernel does not have the required rank")

        # For 3-torsion, [2]R=-R. Compare their affine lifts to obtain lambda_R^3.
        self.delta = {R: self._scale(R, A.double(R)) for R in set(self.generators)}
        pairing = self._cycle(Q, P, S) / self._cycle(P, Q, S)
        pairing *= (self.delta[P] / self.delta[Q]) ** 3
        if pairing != 1:
            raise ValueError("Isogeny kernel is not isotropic")

        # Product coordinates can coincide for different kernel lines.
        # Sum the list with multiplicities, even though delta uses a dictionary.
        return tuple(
            o**3 + 2 * sum(self.delta[R] * R[j] ** 3 for R in self.generators)
            for j, o in enumerate(A.O)
        )

    def set_sign_reference(self, pending_kernel):
        """Use a remaining kernel triple to fix component signs in the codomain."""
        if not self.codomain.is_product:
            raise ValueError("Signed output requires a product codomain")

        product = ProductTheta(self.codomain.O)
        P, Q, S = pending_kernel
        if isinstance(P, CouplePoint):
            difference = P - Q
        else:
            difference = self.domain.diff_add(P, Q, S)

        for anchor in (P, Q, S, difference):
            image = product.lift(self._evaluate_theta(anchor))
            # A component outside E[2] distinguishes a point from its negative.
            if all(2 * image[i] != product.curves[i](0) for i in (0, 1)):
                self.anchor = anchor
                self.image_anchor = image
                self.codomain_product = product
                return

        raise ValueError("Remaining kernel does not provide a product sign reference")

    def __call__(self, P):
        image = self._evaluate_theta(P)
        if self.codomain_product is None:
            return image

        if isinstance(P, CouplePoint):
            translated = P + self.anchor
        else:
            translated = self.domain.sums(P, self.anchor)[0]

        translated_image = self._evaluate_theta(translated)
        return self.codomain_product.recover_signs(
            image, translated_image, self.image_anchor
        )

    def _evaluate_theta(self, P):
        """Evaluate in theta coordinates before recovering codomain signs."""
        if self.domain_product is None:
            P = normalize(self.change(P))
            forms = _cubic_forms(P)
            image = tuple(
                sum(a * f[j] for a, f in zip(self.cubic, forms)) for j in range(4)
            )
            return normalize(image)

        if not isinstance(P, CouplePoint) and not self.diagonal:
            raise UnsupportedProductError(
                "Non-diagonal product evaluation needs signed component lifts"
            )
        signed = self.domain_product.lift(P)
        P = normalize(self.domain_product.split_coords(signed))
        if signed == self.domain_product.zero or any(
            signed in (R, -R) for R in self.signed_generators
        ):
            return self.codomain.O

        total = [p**3 for p in P]
        for R, signed_R in zip(self.generators, self.signed_generators):
            S = normalize(self.domain_product.split_coords(signed + signed_R))
            T = self.source.diff_add(S, R, P)
            c = self._scale(self.source.diff_add(T, R, S), P)
            delta2 = self.delta[R] ** 2
            w = 1 / (c * delta2)

            for j in range(4):
                total[j] += w * S[j] ** 3 + w * w * delta2 * T[j] ** 3

        return normalize(total)


def _cubic_forms(P):
    """The five cubic forms equivariant under the level-2 theta group, as 4-vectors."""
    squares = tuple(c * c for c in P)
    forms = [tuple(P[j] * squares[j] for j in range(4))]
    for a in (1, 2, 3):
        forms.append(tuple(P[j] * squares[j ^ a] for j in range(4)))
    forms.append(tuple(P[j ^ 1] * P[j ^ 2] * P[j ^ 3] for j in range(4)))
    return tuple(forms)


@cached_function
def _strategy(n):
    # Dynamic programming trades triplings against point pushes (cubic forms,
    # measured at about twice a tripling). The weights affect speed only.
    choices = {1: ()}
    costs = {1: 0}

    for size in range(2, n + 1):
        cost, split = min(
            (costs[size - b] + costs[b] + b + 2 * (size - b), b)
            for b in range(1, size)
        )
        choices[size] = (split,) + choices[size - split] + choices[split]
        costs[size] = cost

    return choices[n]


class ThreeIsogenyChain:
    """Reusable (3^e,3^e)-map; transfer generators and their sum together.

    Intermediate products retain signed elliptic lifts aligned by a translated
    image from the preceding step. This preserves coprime bases and their sums.
    """

    @classmethod
    def from_degree(cls, O, kernel, degree, perform_checks=True):
        """Construct a chain from its degree rather than its exponent."""
        degree = ZZ(degree)
        exponent = degree.valuation(3) if degree > 1 else 0
        if degree < 1 or degree != 3**exponent:
            raise ValueError("Isogeny degree must be a power of 3")
        return cls(O, kernel, exponent, perform_checks)

    def __init__(self, O, kernel, exponent, perform_checks=True):
        exponent = ZZ(exponent)
        if exponent < 0:
            raise ValueError("Use a nonnegative power of 3")

        A = ThetaArithmetic(O)
        self.domain = A
        self._maps = []
        if exponent == 0:
            self.codomain = A
            return

        if len(kernel) not in (2, 3):
            raise ValueError("Supply two generators and optionally their sum")
        if len(kernel) == 2:
            P, Q = kernel
            if A.is_product:
                if not all(isinstance(T, CouplePoint) for T in kernel):
                    raise UnsupportedProductError(
                        "Product kernels need signed generators or a supplied P+Q"
                    )
                S = P + Q
            else:
                S = A.sums(P, Q)[0]
            kernel = (P, Q, S)

        if A.is_product:
            product = ProductTheta(A.O)
            kernel = product.kernel(kernel)
        else:
            kernel = tuple(normalize(P) for P in kernel)

        if perform_checks:
            d = 3**exponent
            zero = product.zero if A.is_product else A.O

            def mul(n, P):
                if isinstance(P, CouplePoint):
                    return n * P
                return A.mul(n, P)

            if any(mul(d, P) != zero or mul(d // 3, P) == zero for P in kernel):
                raise ValueError("Kernel points must have exact requested order")
            if not A.is_product and kernel[2] not in A.sums(kernel[0], kernel[1]):
                raise ValueError("Kernel sum is inconsistent with its generators")

        strategy = _strategy(exponent)
        strat_idx = 0
        levels = [0]
        kernel_elements = [kernel]

        for k in range(exponent):
            prev = sum(levels)
            current = kernel_elements[-1]

            # Descend to 3-torsion, saving generators needed by later steps.
            while prev != exponent - 1 - k:
                count = strategy[strat_idx]
                next_kernel = []
                for P in current:
                    if isinstance(P, CouplePoint):
                        next_kernel.append(3**count * P)
                    else:
                        next_kernel.append(A.triple_iter(P, count))
                current = tuple(next_kernel)
                levels.append(count)
                kernel_elements.append(current)
                prev += count
                strat_idx += 1

            phi = ThetaThreeIsogeny(A, current, perform_checks)
            kernel_elements.pop()
            levels.pop()
            if phi.codomain.is_product and kernel_elements:
                phi.set_sign_reference(kernel_elements[-1])

            self._maps.append(phi)
            kernel_elements = [
                tuple(phi(P) for P in triple) for triple in kernel_elements
            ]
            if phi.codomain_product is not None:
                kernel_elements = [
                    phi.codomain_product.kernel(triple) for triple in kernel_elements
                ]
            A = phi.codomain

        self.codomain = A

    def __call__(self, P):
        if not self._maps:
            if isinstance(P, CouplePoint):
                return self.domain.product_coordinates.encode(P)
            return normalize(P)
        if self.domain.is_product and not isinstance(P, CouplePoint):
            raise UnsupportedProductError(
                "A chain starting on a product needs a signed CouplePoint"
            )

        if not isinstance(P, CouplePoint):
            P = normalize(P)
        for phi in self._maps:
            P = phi(P)

        return tuple(P)
