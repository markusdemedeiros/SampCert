#!/usr/bin/env python3

# Benchmarking the discrete Gaussian sampler

import matplotlib.pyplot as plt
import timeit
import secrets
import numpy as np
from datetime import datetime
import tqdm as tqdm
import argparse
from diffprivlib.mechanisms import GaussianDiscrete
import subprocess

def gaussian_benchmarks(mix, warmup_attempts, measured_attempts, lb ,ub, quantity, inv):
    ub=50
    quantity=1

    # Values of epsilon attempted
    sigmas = []
    nbytes = []

    g = GaussianDiscrete(epsilon=0.01, delta=0.00001)

    for sigma_ in tqdm.tqdm(range(lb,ub,quantity)):
        if inv:
            sigma = 1.0 / float(sigma_)
            sigma_num = sigma_
            sigma_denom = ub
        else: 
            sigma = sigma_
            sigma_num = sigma_
            sigma_denom = 1

        g._scale = sigma
        sigmas += [sigma]

        sigma_squared = sigma ** 2

        num_attempts=1000
        total = 0
        result = subprocess.run(['./.lake/build/bin/profile', str(sigma_num), str(sigma_denom), str(num_attempts)], stdout=subprocess.PIPE)
        nbytes += [float(len(str(result.stdout)) - 3) / float(num_attempts)]

    fig,ax1 = plt.subplots(figsize=(7,5))
    # only one line may be specified; full height
    plt.axvline(x = 4, linestyle="--", color = 'gray', linewidth=0.5)
    plt.axvline(x = 8, linestyle="--", color = 'gray', linewidth=0.5)
    plt.axvline(x = 16, linestyle="--", color = 'gray', linewidth=0.5)
    plt.axvline(x = 32, linestyle="--", color = 'gray', linewidth=0.5)
    ax1.plot(sigmas, nbytes, linewidth=1.0, color="black")
    ax1.set_xlabel("Sigma")
    ax1.set_ylabel("Average number of bytes")
    now = datetime.now()
    filename = 'GaussianProfile.pdf'
    plt.savefig(filename)



if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--mix", nargs="+", type=int, help="mix", default=[7])
    parser.add_argument("--warmup", type=int, help="warmup", default=0)
    parser.add_argument("--trials", type=int, help="trials", default=20)
    parser.add_argument("--min", type=int, help="min", default=1)
    parser.add_argument("--max", type=int, help="max", default=500)
    parser.add_argument("--quantity", type=int, help="step", default=10)
    parser.add_argument("--inv", default=False, action=argparse.BooleanOptionalAction)
    args = parser.parse_args()

    gaussian_benchmarks(args.mix,args.warmup,args.trials,args.min,args.max,args.quantity,args.inv)
