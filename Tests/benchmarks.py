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
from discretegauss import sample_dgauss

import SampCert
from Load import SampCertFII_dgs_get
# from Load import samplers

sampler = SampCert.SLang()
rng = secrets.SystemRandom()

def gaussian_benchmarks(mix, warmup_attempts, measured_attempts, lb ,ub, quantity, inv):
    # Values of epsilon attempted
    sigmas = []

    g = GaussianDiscrete(epsilon=0.01, delta=0.00001)

    # Mixes to force the benchmark to work with algorithm 1 or algorithm 2 
    mix = [0, 300, 7]
    titles = ["DiscreteGaussianSample + Algorithm 1 ",
              "DiscreteGaussianSample + Algorithm 2",
              "DiscreteGaussianSample + Optimized "]


    # SampCert
    means = []
    stdevs = []
    for i in mix:
        means.append([])
        stdevs.append([])

    # FFI SampCert
    ffimeans = []
    ffistdevs = []

    # sample_dgauss
    ibm_dg_mean = []
    ibm_dg_stdev = []

    # DiffPrivLib GaussianDiscrete
    ibm_dpl_mean = []
    ibm_dpl_stdev = []

    num_attempts = warmup_attempts + measured_attempts

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

        times = []
        ffitimes = []
        for i in mix:
            times.append([])        

        t_ibm_dg = []
        t_ibm_dpl = []
         
        for m in range(len(mix)): 
            for i in range(num_attempts):
                start_time = timeit.default_timer()
                sampler.DiscreteGaussianSample(sigma_num, sigma_denom, mix[m])
                elapsed = timeit.default_timer() - start_time
                times[m].append(elapsed)

        for i in range(num_attempts):
            start_time = timeit.default_timer()
            SampCertFII_dgs_get(sigma_num, sigma_denom, 7)
            elapsed = timeit.default_timer() - start_time
            ffitimes.append(elapsed)

        for i in range(num_attempts):
            start_time = timeit.default_timer()
            sample_dgauss(sigma_squared, rng)
            elapsed = timeit.default_timer() - start_time
            t_ibm_dg.append(elapsed)

        for i in range(num_attempts):
            start_time = timeit.default_timer()
            g.randomise(0)
            elapsed = timeit.default_timer() - start_time
            t_ibm_dpl.append(elapsed)

        measured = []
        # Compute mean and stdev
        for m in range(len(mix)): 
            measured.append(np.array(times[m][-measured_attempts:]))
        ibm_dg_measured = np.array(t_ibm_dg[-measured_attempts:])
        ibm_dpl_measured = np.array(t_ibm_dpl[-measured_attempts:])
        ffi_measured = np.array(ffitimes[-measured_attempts:])

        # Convert s to ms
        for m in range(len(mix)): 
            means[m].append(measured[m].mean() * 1000.0)
            stdevs[m].append(measured[m].std() * 1000.0)
        ibm_dg_mean.append(ibm_dg_measured.mean() * 1000.0)
        ibm_dg_stdev.append(ibm_dg_measured.std() * 1000.0)
        ibm_dpl_mean.append(ibm_dpl_measured.mean() * 1000.0)
        ibm_dpl_stdev.append(ibm_dpl_measured.std() * 1000.0)
        ffimeans.append(ffi_measured.mean() * 1000.0)
        ffistdevs.append(ffi_measured.std() * 1000.0)

    fig,ax1 = plt.subplots(figsize=(7,5))

    color = plt.cm.rainbow(np.linspace(0, 1, len(mix) + 2))

    ibm_confidence = 1.96 * np.array(ibm_dg_mean) / np.sqrt(measured_attempts)
    ax1.plot(sigmas, ibm_dg_mean, color=color[0], linewidth=1.0, label='sample_dgauss (Algorithm 1)', linestyle=(0, (3,1,1,1)))
    ax1.fill_between(sigmas, np.array(ibm_dg_mean)-ibm_confidence, np.array(ibm_dg_mean)+ibm_confidence,
                     alpha=0.2, facecolor=color[0], linewidth=2, linestyle='solid', antialiased=True)

    ibm_dpl_confidence = 1.96 * np.array(ibm_dpl_mean) / np.sqrt(measured_attempts)
    ax1.plot(sigmas, ibm_dpl_mean, color=color[1], linewidth=1.0, label='diffprivlib (Algorithm 2)', linestyle=(0, (5, 4)))
    ax1.fill_between(sigmas, np.array(ibm_dpl_mean)-ibm_dpl_confidence, np.array(ibm_dpl_mean)+ibm_dpl_confidence,
                     alpha=0.2, facecolor=color[1], linewidth=2, linestyle='solid', antialiased=True)

    linestyles = [(0, (5, 2)), 'dotted', 'solid']
    for m in range(len(mix)):
        confidence = 1.96 * np.array(stdevs[m]) / np.sqrt(measured_attempts)
        ax1.plot(sigmas, means[m], color=color[2 + m], linewidth=1.0, label=titles[m], linestyle=(linestyles[m]))
        ax1.fill_between(sigmas, np.array(means[m])-confidence, np.array(means[m])+confidence,
                        alpha=0.2, facecolor=color[2 + m], linewidth=2, linestyle='solid', antialiased=True)

    ffi_confidence = 1.96 * np.array(ffimeans) / np.sqrt(measured_attempts)
    ax1.plot(sigmas, ffimeans, color='purple', linewidth=1.5, label='Compiled (Optimized)')
    ax1.fill_between(sigmas, np.array(ffimeans)-ffi_confidence, np.array(ffimeans)+ffi_confidence,
                     alpha=0.2, facecolor='purple', linewidth=2, linestyle='solid', antialiased=True)

    ax1.set_xlabel("Sigma")
    ax1.set_ylabel("Sampling Time (ms)")
    plt.legend(loc = 'best')
    now = datetime.now()
    filename = 'GaussianBenchmarks.pdf'
    print(filename)
    plt.savefig(filename)

if __name__ == "__main__":

    parser = argparse.ArgumentParser()
    parser.add_argument("--mix", nargs="+", type=int, help="mix", default=[7])
    parser.add_argument("--warmup", type=int, help="warmup", default=0)
    parser.add_argument("--trials", type=int, help="trials", default=1000)
    parser.add_argument("--min", type=int, help="min", default=1)
    parser.add_argument("--max", type=int, help="max", default=500)
    parser.add_argument("--quantity", type=int, help="step", default=10)
    parser.add_argument("--inv", default=False, action=argparse.BooleanOptionalAction)
    args = parser.parse_args()

    gaussian_benchmarks(args.mix,args.warmup,args.trials,args.min,args.max,args.quantity,args.inv)
