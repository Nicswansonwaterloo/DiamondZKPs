# DiamondZKPs

This repository contains SageMath research implementations of zero-knowledge
proofs of knowledge for isogeny diamonds between supersingular elliptic
curves. It covers three protocol families—**Cube-ZKP**, **Windmill-ZKP**, and
**Kani-Diamond-ZKP**—as well as the **Kube-ZKP** variant of Cube-ZKP. The code
includes key-generation, prover, and verifier routines; parameter generation;
benchmark drivers; proof-cost estimates; and the one- and two-dimensional
isogeny computations used by the protocols.

These are research prototypes, not production cryptographic implementations.
The secret keys and transcripts are deliberately verbose, and the code uses
SageMath's random-number facilities rather than a production cryptographic
random-number generator.

## Performance

These research implementations are not currently practical. The available
two-dimensional isogeny routines are particularly slow. Replacing them with
highly performant alternatives is left as future work.

| Protocol | Security | Prover | Verifier |
|---|---:|---:|---:|
| Cube-ZKP | 128 bits | 162 s | 62 s |
| Kube-ZKP | 128 bits | 510 s | 109 s |
| Kani-ZKP | 128 bits | 281 s | 325 s |
| Kani-Heuristic | 128 bits | 98 s | 119 s |

Measured on 2026-10-01 with SageMath 10.9 on an Apple M4 Max averaged over 10 trials.
Windmill-ZKP was not benchmarked at 128-bit security because the corresponding
M-SIDH prime exceeds 5,000 bits and is generally incomparable.

## Running the code

The repository was checked with SageMath 10.9. Activate a Python environment
that provides SageMath, then run commands from the repository root so that
imports from `helpers` and `vendors` resolve. 

Run the 128-bit benchmarks with:

```sh
python cube_bench.py --trials 10 --workers 10
python kube_bench.py --trials 10 --workers 10
python kani_bench.py --trials 10 --workers 10
python kani_bench.py --heuristic --trials 10 --workers 10
```

Run the assertion-based proof-of-concept checks with:

```sh
python windmill_proof_of_concept.py
python kani_proof_of_concept.py
```

The $(3,3)$ chains support intermediate products and coprime-point transfer.
Product evaluations need signed `CouplePoint` inputs to preserve component
signs. Run `python two_dim_isogeny_checks.py` for the focused correctness checks.

## File organisation

- `cube_optimized.py` implements the seven-challenge Cube-ZKP using
  x-coordinate-only Kummer lines. `cube_proof_of_concept.py` is the direct
  elliptic-curve prototype and retains the older eight-challenge transcript.
- `cube_params.py` generates Cube parameters and contains the embedded 128-bit
  and smoke-test parameter sets. `cube_bench.py` benchmarks the optimized
  implementation.
- `kube_optimized.py` implements the five-challenge Kube-ZKP variant.
  `kube_params.py` contains its parameter generation and embedded parameter
  sets, and `kube_bench.py` is its benchmark driver.
- `windmill_proof_of_concept.py` is the executable Windmill-ZKP prototype with
  small embedded parameters and assertion-based verification checks.
- `kani_proof_of_concept.py` is the direct Kani-Diamond-ZKP prototype with small
  embedded parameters. `kani_semi_optimized.py` uses the vendored `RanIso`
  construction, and `kani_params.py` generates and stores its parameter sets.
  `kani_bench.py` benchmarks the standard and heuristic parameter sets.
- `estimated_isogs.py` contains the handwritten proof-size and isogeny-count
  calculations used for protocol comparisons.
- `helpers/` contains project-owned elliptic-curve, Kummer-line, hashing,
  torsion-basis, and one- and two-dimensional isogeny utilities.
- `vendors/` contains the third-party SageMath code described below.
- `LICENSE` contains the license for the project-owned code.

## Third-party code

- `vendors/Theta_SageMath/` is vendored from the
  [ThetaIsogenies/two-isogenies](https://github.com/ThetaIsogenies/two-isogenies)
  repository (subdirectory `Theta-SageMath`) and is used under the MIT License.
  Copyright belongs to the original authors; see
  `vendors/Theta_SageMath/LICENSE`.
- `vendors/Kummer_Isogeny/` is vendored from
  [GiacomoPope/KummerIsogeny](https://github.com/GiacomoPope/KummerIsogeny)
  and is used under the MIT License. Copyright belongs to the original authors;
  see `vendors/Kummer_Isogeny/LICENSE`.
- `vendors/SQIsign2DSquare/` is a Sage/Python port of the `RanIso` path from
  [Kaizhan-Lin/SQIsign2DSquare](https://github.com/Kaizhan-Lin/SQIsign2DSquare)
  and is used under the MIT License. Copyright belongs to the original authors;
  see `vendors/SQIsign2DSquare/LICENSE` and
  `vendors/SQIsign2DSquare/README.md`.
