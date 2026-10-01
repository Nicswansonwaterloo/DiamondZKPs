import argparse
import multiprocessing

from kani_params import KANI_128_PARAMS, KANI_128_PARAMS_HEUR
from kani_semi_optimized import run_trial
from vendors.Theta_SageMath.utilities.utils import speed_up_sagemath


def run_benchmark_trial(trial_num, num_trials, params):
    speed_up_sagemath()
    print(f"\n=== Trial {trial_num + 1} ===", flush=True)
    prover_time, verifier_time = run_trial(trial_num, num_trials, params)
    print(
        f"Trial {trial_num + 1}: prover: {prover_time:.4f}s; verifier: {verifier_time:.4f}s",
        flush=True,
    )
    return prover_time, verifier_time


def run_trials(params, num_trials, num_workers=None):
    trial_args = [(i, num_trials, params) for i in range(num_trials)]
    if num_workers is not None:
        with multiprocessing.Pool(processes=num_workers) as pool:
            results = pool.starmap(run_benchmark_trial, trial_args)
    else:
        results = [run_benchmark_trial(*args) for args in trial_args]

    avg_prove = sum(prove_time for prove_time, _ in results) / num_trials
    avg_verify = sum(verify_time for _, verify_time in results) / num_trials
    num_reps = params[8]
    print("\n=== Results ===")
    print(f"Avg proof time  : {avg_prove:.2f}s  ({avg_prove * num_reps:.2f}s at {num_reps} reps)")
    print(f"Avg verify time : {avg_verify:.2f}s  ({avg_verify * num_reps:.2f}s at {num_reps} reps)")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Time Kani ZKP proof and verification.")
    parser.add_argument(
        "--trials", type=int, default=3,
        help="Number of trials to run (default: 3)"
    )
    parser.add_argument(
        "--workers", type=int, default=None, metavar="N",
        help="Number of parallel worker processes (default: no multiprocessing)"
    )
    parser.add_argument(
        "--heuristic", action="store_true",
        help="Use the heuristic 128-bit parameter set"
    )
    args = parser.parse_args()
    if args.trials < 1:
        parser.error("--trials must be positive")
    if args.workers is not None and args.workers < 1:
        parser.error("--workers must be positive")

    params = KANI_128_PARAMS_HEUR if args.heuristic else KANI_128_PARAMS
    run_trials(params, args.trials, args.workers)
