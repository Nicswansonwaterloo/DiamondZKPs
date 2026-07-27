import argparse
import gc
import multiprocessing
import time

from kube_optimized import NUM_CHALLENGES, key_gen, prover, verifier
from kube_params import KUBE_128_PARAMS
from vendors.Kummer_Isogeny.kummer_line import KummerLine, KummerPoint
from vendors.Theta_SageMath.utilities.utils import speed_up_sagemath

params = KUBE_128_PARAMS  # Change here to select security level.


def clear_kummer_caches():
    for obj in gc.get_objects():
        if isinstance(obj, (KummerLine, KummerPoint)):
            for key in list(obj.__dict__.keys()):
                if key.startswith('_cache__'):
                    del obj.__dict__[key]


def run_trial(args):
    trial_num, params = args
    speed_up_sagemath()
    print(f"\n=== Trial {trial_num + 1} ===")

    sk, pk = key_gen(params)
    times = []

    for challenge in range(NUM_CHALLENGES):
        t0 = time.time()
        commitments, responses = prover(params, sk, pk)
        t1 = time.time()

        clear_kummer_caches()

        t2 = time.time()
        assert verifier(params, pk, challenge, responses[challenge], commitments), (
            f"Verification failed for challenge {challenge}"
        )
        t3 = time.time()

        times.append((t1 - t0, t3 - t2))

    return times


def print_results(results, num_trials, num_reps):
    print("\n=== Results ===")
    print("Average verification time per challenge:")
    avg_verify = 0
    for challenge in range(NUM_CHALLENGES):
        avg = sum(results[t][challenge][1] for t in range(num_trials)) / num_trials
        print(f"  Challenge {challenge}: {avg:.4f}s")
        avg_verify += avg
    avg_verify /= NUM_CHALLENGES

    avg_prove = sum(
        sum(prove_t for prove_t, _ in results[t]) / NUM_CHALLENGES
        for t in range(num_trials)
    ) / num_trials

    print(f"\nAvg proof time  : {avg_prove:.2f}s  ({avg_prove * num_reps:.2f}s at {num_reps} reps)")
    print(f"Avg verify time : {avg_verify:.2f}s  ({avg_verify * num_reps:.2f}s at {num_reps} reps)")


def run_trials(params, num_trials, num_workers=None):
    trial_args = [(i, params) for i in range(num_trials)]

    if num_workers is not None:
        with multiprocessing.Pool(processes=num_workers) as pool:
            results = pool.map(run_trial, trial_args)
    else:
        results = [run_trial(a) for a in trial_args]

    print_results(results, num_trials, params[8])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Time Kube ZKP proof and verification.")
    parser.add_argument(
        "--trials", type=int, default=3,
        help="Number of trials to run (default: 3)"
    )
    parser.add_argument(
        "--workers", type=int, default=None, metavar="N",
        help="Number of parallel worker processes (default: no multiprocessing)"
    )
    args = parser.parse_args()

    run_trials(params, args.trials, args.workers)
