from sage.all import log, var
from sympy import RR

lam = var("λ")

def elliptic_curve_size(prime_size):
    return 2 * prime_size # one j-invariant in Fp2

def point_size(prime_size):
    # Using montgomery reps, one Fp2 element.
    return 2 * prime_size

def theta_coord_size(prime_size):
    # One normalized P3 element over Fp2: three Fp2 coordinates.
    return 3 * point_size(prime_size)

def commitment_hash_size(num_commitment_hashes):
    # Each commitment hash is 2\lambda bits, and we have 2*num_commitment_hashes of them. (Can be reduced via compressed fiat shamir, but we don't consider that here.)
    return 2 * num_commitment_hashes * lam

def soundness_repititions(num_challenges):
    # Compute the coefficient of lambda for a generic n-sound proof.
    return lam / log(num_challenges / (num_challenges - 1), 2)

def walk_length(isog_degree, ell):
    # Given an isogeny degree, find exponent such that ell^s = isog_degree.
    return log(isog_degree, ell)

def stringify(expression):
    p = expression.simplify_full().expand()
    terms = [(RR(p.coefficient(lam, i)), i) for i in (2, 1, 0)]
    return " ".join(
        f"{'+' if c > 0 and j else '-' if c < 0 else ''} {abs(c):.2f}*λ^{i}"
        for j, (c, i) in enumerate(x for x in terms if x[0])
    ).strip()

###########################
#### CUBE CALCULATIONS ####
###########################
print("\n#####CUBE#####\n")
num_challanges = 7
num_reps = soundness_repititions(num_challanges)

print(f"Soundness repetitions: {stringify(num_reps)}")

prime_size = 6 * lam
# We assume the best known attack against DSSP is sqrt, so we take isog_degree to be 2^(2\lambda)
A_isogeny_length = walk_length(2**(2 * lam), 2)
B_isogeny_length = walk_length(2**(2 * lam), 3)
C_isogeny_length = walk_length(2**(2 * lam), 5)

# Number of Isogeny computations
# -- Prover -- 
num_A_isogenies = 1 # (see cube_optimized.py)
num_B_isogenies = 2 # (see cube_optimized.py)
num_C_isogenies = 1 # (see cube_optimized.py)
print(f"Prover 2-isogenies: {stringify(num_reps * A_isogeny_length * num_A_isogenies)}")
print(f"Prover 3-isogenies: {stringify(num_reps * B_isogeny_length * num_B_isogenies)}")
print(f"Prover 5-isogenies: {stringify(num_reps * C_isogeny_length * num_C_isogenies)}") 
# -- Verifier (across all challenges) --
# A isogenies: 1 (see cube_optimized.py)
# B isogenies: 2 (see cube_optimized.py)
# C isogenies: 4 (see cube_optimized.py)
num_A_isogenies = 1 / 7
num_B_isogenies = 2 / 7
num_C_isogenies = 4 / 7
print(f"Verifier 2-isogenies: {stringify(num_reps * A_isogeny_length * num_A_isogenies)}")
print(f"Verifier 3-isogenies: {stringify(num_reps * B_isogeny_length * num_B_isogenies)}")
print(f"Verifier 5-isogenies: {stringify(num_reps * C_isogeny_length * num_C_isogenies)}")

# Average Proof size (across all challenges):
# Number of commitment hashes:
#  Total: 9
# Number of elliptic curves: 
#  - 1 for the first 4 challenges
#  - 2 for the last 3 challenges
#  Total: 10
# Number of points:
#  - 3 for first 4 challenges
#  - 13 in challenge 4
#  - 9 in challenges 5 and 6
#  Total: 43
# Number of Nonces:
#  - 2 for first 4 challenges
#  - 5 in challenge 4
#  - 4 in challenges 5 and 6
#  Total: 21
# Number of scalars:
#  - 2 mod C for first 4 challenges
#  - 2 mod B for 2 challenges
#  Total: 12
one_round_proof_size = (
    commitment_hash_size(9)
    + (10 / num_challanges) * elliptic_curve_size(prime_size)
    + (43 / num_challanges) * point_size(prime_size)
    + (21 / num_challanges) * 2 * lam # Nonces are 2\lambda bits
    + (12 / num_challanges) * 2 * lam # Scalars are 2\lambda bits.
)
one_round_proof_size_bytes = (one_round_proof_size * num_reps) / 8
print(f"Cube proof size: {stringify(one_round_proof_size_bytes)} bytes")

###########################
#### KUBE CALCULATIONS ####
###########################
print("\n#####KUBE#####\n")
num_challanges = 5
num_reps = soundness_repititions(num_challanges)

print(f"Soundness repetitions: {stringify(num_reps)}")
prime_size = 6 * lam
# We recall that due to soundness losses, we must take C \approx N^2. We also assume the best known attack against DSSP is sqrt
N_isogeny_length = walk_length(2**(2 * lam), 2)
C_isogeny_length = walk_length(2**(4 * lam), 3)

# Number of Isogeny computations
# -- Prover --
num_C_isogenies = 2
num_NN_isogenies = 1
print(f"Prover 3-isogenies: {stringify(num_reps * C_isogeny_length * num_C_isogenies)}")
print(f"Prover (2, 2)-isogenies: {stringify(num_reps * N_isogeny_length * num_NN_isogenies)}")
# -- Verifier (avg across all challenges) --
num_C_isogenies = 4 / num_challanges
num_NN_isogenies = 1 / num_challanges
print(f"Verifier 3-isogenies: {stringify(num_reps * C_isogeny_length * num_C_isogenies)}")
print(f"Verifier (2, 2)-isogenies: {stringify(num_reps * N_isogeny_length * num_NN_isogenies)}")

# Proof size (across all challenges):
# Number of commitment hashes:
#  Total: 6
# Number of elliptic curves: 
#  - 1 for first 4 challanges
#  - 4 for the last challange 
# Total: 8
# Number of points:
#  - 3 for first 4 challenges
#  - 12 Kummer points and 2 CouplePoints = 16 points for the last challenge
#  Total: 28
# Number of Nonces:
#  - 2 for each of the first 4 challenges
#  - 5 for the last challenge
#  Total: 13
# Number of scalars:
#  - 2 mod C for first 4 challenges
#  Total: 8
one_round_proof_size = (
    commitment_hash_size(6)
    + (8 / num_challanges) * elliptic_curve_size(prime_size)
    + (28 / num_challanges) * point_size(prime_size)
    + (13 / num_challanges) * 2 * lam # Nonces are 2\lambda bits
    + (8 / num_challanges) * 4 * lam # Scalars are 4\lambda bits (mod C).
)
one_round_proof_size_bytes = (one_round_proof_size * num_reps) / 8
print(f"Kube proof size: {stringify(one_round_proof_size_bytes)} bytes")

###########################
#### KANI CALCULATIONS ####
###########################
print("\n#####KANI#####\n")
num_challanges = 3
num_reps = soundness_repititions(num_challanges)

print(f"Soundness repetitions: {stringify(num_reps)}")

prime_size = 8 * lam
# We recall that we must take M \approx N^22^{2\lambda} to reduce one challange to hard DLIT instance.
N_isogeny_length = walk_length(2**(2 * lam), 2)
M_isogeny_length = walk_length(2**(6 * lam), 3)

# Number of Isogeny computations
# -- Prover --
num_M_isogenies = 2
num_NN_isogenies = 1
print(f"Prover 3-isogenies: {stringify(num_reps * M_isogeny_length * num_M_isogenies)}")
print(f"Prover (2, 2)-isogenies: {stringify(num_reps * N_isogeny_length * num_NN_isogenies)}")
# -- Verifier (avg across all challenges) --
num_3_isogenies = 2 / num_challanges
num_22_isogenies = 1 / num_challanges
num_33_isogenies = 1 / num_challanges
print(f"Verifier 3-isogenies: {stringify(num_reps * M_isogeny_length * num_3_isogenies)}")
print(f"Verifier (2, 2)-isogenies: {stringify(num_reps * N_isogeny_length * num_22_isogenies)}")
print(f"Verifier (3, 3)-isogenies: {stringify(num_reps * M_isogeny_length * num_33_isogenies)}")

# Proof size (across all challenges):
# Number of commitment hashes:
#  Total: 4
# Number of elliptic curves: 
#  - 2 for first challenge
#  - 2 for last challenge
#  Total: 4
# Number of Theta coordinates:
#  - 1 for codomain in second and third challange
#  - 6 theta coords in second and third challange
# Total: 14
# Number of elliptic curve points:
#  - 6 for first challenge
#  - 6 for last challenge
# Total: 12
# Number of Nonces:
#  - 2 for first challenge
#  - 2 for second challenge
#  - 3 for last challenge
#  Total: 7
# Number of scalars:
#  - 8 for first and second challange
#  Total: 16
one_round_proof_size = (
    commitment_hash_size(4)
    + (4/num_challanges) * elliptic_curve_size(prime_size)
    + (14/num_challanges) * theta_coord_size(prime_size)
    + (12/num_challanges) * point_size(prime_size)
    + (7/num_challanges) * 2 * lam # Nonces are 2\lambda bits
    + (16/num_challanges) * 6 * lam # Scalars are 6\lambda bits (mod M).
)
one_round_proof_size_bytes = (one_round_proof_size * num_reps) / 8
print(f"Kani proof size: {stringify(one_round_proof_size_bytes)} bytes")

#####################################
#### KANI Heuristic CALCULATIONS ####
#####################################
print("\n#####KANI HEURISTIC#####\n")
# Same analysis, but with M^2 \approx N^2 2^{2\lambda}.
print(f"Soundness repetitions: {stringify(num_reps)}")

prime_size = 5 * lam
# We recall that we must take M \approx N^22^{2\lambda} to reduce one challange to hard DLIT instance.
N_isogeny_length = walk_length(2**(2 * lam), 2)
M_isogeny_length = walk_length(2**(3 * lam), 3)
# Below this line is a copy and paste from the KANI calculations, but using the new length values.
# Number of Isogeny computations
# -- Prover --
num_M_isogenies = 2
num_NN_isogenies = 1
print(f"Prover 3-isogenies: {stringify(num_reps * M_isogeny_length * num_M_isogenies)}")
print(f"Prover (2, 2)-isogenies: {stringify(num_reps * N_isogeny_length * num_NN_isogenies)}")
# -- Verifier (avg across all challenges) --
num_3_isogenies = 2 / num_challanges
num_22_isogenies = 1 / num_challanges
num_33_isogenies = 1 / num_challanges
print(f"Verifier 3-isogenies: {stringify(num_reps * M_isogeny_length * num_3_isogenies)}")
print(f"Verifier (2, 2)-isogenies: {stringify(num_reps * N_isogeny_length * num_22_isogenies)}")
print(f"Verifier (3, 3)-isogenies: {stringify(num_reps * M_isogeny_length * num_33_isogenies)}")

# Proof size (across all challenges):
# Number of commitment hashes:
#  Total: 4
# Number of elliptic curves: 
#  - 2 for first challenge
#  - 2 for last challenge
#  Total: 4
# Number of Theta coordinates:
#  - 1 for codomain in second and third challange
#  - 6 theta coords in second and third challange
# Total: 14
# Number of elliptic curve points:
#  - 6 for first challenge
#  - 6 for last challenge
# Total: 12
# Number of Nonces:
#  - 2 for first challenge
#  - 2 for second challenge
#  - 3 for last challenge
#  Total: 7
# Number of scalars:
#  - 8 for first and second challange
#  Total: 16
one_round_proof_size = (
    commitment_hash_size(4)
    + (4/num_challanges) * elliptic_curve_size(prime_size)
    + (14/num_challanges) * theta_coord_size(prime_size)
    + (20/num_challanges) * point_size(prime_size)
    + (7/num_challanges) * 2 * lam # Nonces are 2\lambda bits
    + (16/num_challanges) * 3 * lam # Scalars are 3\lambda bits (mod M).
)
one_round_proof_size_bytes = (one_round_proof_size * num_reps) / 8
print(f"Kani Heuristic proof size: {stringify(one_round_proof_size_bytes)} bytes")
