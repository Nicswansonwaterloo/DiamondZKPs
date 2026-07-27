# SQIsign2DSquare Sage port

This directory contains a native Sage/Python port of the full-degree
`RanIso` path from Kaizhan Lin's Julia
[`SQIsign2DSquare`](https://github.com/Kaizhan-Lin/SQIsign2DSquare).

The port was scaffolded by an LLM and modified by the author of this repository. 
It mostly follows these original files and keeps their function names and
procedural organization where practical:

- `src/quaternion/order.jl`
- `src/quaternion/cornacchia.jl`
- `src/quaternion/klpt.jl` (`FullRepresentInteger`)
- `src/rii/quat_action.jl`
- `src/rii/d2isogeny.jl`
- `src/rii/rii.jl` (`RanIso`, not `ImRanIso`)

We replace Julia's projective Montgomery implementation with Sage elliptic
curve points and the repository's vendored theta formulas. It is a TODO
to replace the elliptic curve formulas with vendored kummer library similarly.

For integration with DiamondZKPs, the parameter precomputation accepts

```
p + 1 = 4 * 2^e2 * 3^e3.
```

Here `2^e2` is the degree used by `RanIso`; the two additional rational
2-torsion levels provide order-`4 * 2^e2` points for DiamondZKPs' existing
`EllipticProductIsogeny`-style prover and verifier helpers. The native RanIso
port itself retains the Julia implementation's `product_isogeny_sqrt` chain,
which only requires the kernel of order `2^e2`.


The implementation is currently limited to the exact prime shape
above and to `3^e3` as the accessible odd degree.
