# SampCert Artifact

Our artifact consists of 
- The Lean 4 source code for SampCert, including all proofs mentioned in the paper, and a code extractor used to translate the samplers into Python. 
- A script to benchmark the extracted SampCert samplers against other DP implementations.
- A script to profile the number of bytes consumed by the discrete Gaussian sampler.
- A script to run stastical tests on the extracted SampCert samplers. 
- A Lean 4 program to run stastical tests on the SampCert samplers and example DP queries, using the Lean FFI. 

## Building

To build and enter the artifact, run the following commands. 
```
docker build -t sampcert --platform linux/arm64,linux/amd64 .
docker run -it sampcert -name sampcert /bin/bash
```
This will compile our Lean code, and extract the implementation of our samplers used by our Large Cloud Provider. 


## The Lean code

The file `SampCert.lean` is the top-level file in the project. 
To check that `definition-name` code is sorry-free, one can add the line 
```
#print axioms definition-name
```
to any file and recompile with `lake build`. 
For example, uncommenting `-- #print axioms combineMeanHistogram` at the bottom of `SampCert.lean` will print 
```
[2165/2166] Built SampCert
info: ././././SampCert.lean:75:0: 'combineMeanHistogram' depends on axioms: [propext, Classical.choice, Quot.sound]
```
which does not include the axiom `sorryAx`, indicating that the definition and proof is closed. 

The file ``paper_mapping.md`` includes a table that lists all of the definitions from our paper. 

## Benchmarks

To reproduce our benchmarks (figure 4), run the following command from the home directory inside the artifact: 
```
sh SampCert/Tests/run_benchmark.sh
```
This command will save a reproduction of figure 4 to the home directory. It can be accessed by running the following command outside of the artifact.
```
docker cp sampcert:/home/lean/GaussianBenchmarks.pdf .
```

To profile the number of bytes of entropy consumed, we have a version of the code instrumented with logging on a separate branch (``git diff main..PLDI25-profiling`` will show you the differences). 
To produce a figure that counts the number of bytes of entropy consumed, run the following:
```
git checkout PLDI25-profiling
lake build 
python3 profile.py 
```
To view the profile, it can be copied out of the container as above:
```
docker cp sampcert:/home/lean/GaussianProfile.pdf .
```


## Statistical Tests: Extracted samplers

To check that our extracted samplers execute and sample from the correct distribution, we have included a K-S test.
To run the tests on the extrated versions, run the following:
```
python3 Tests/SampCert-py/testing-kolmogorov-discretegaussian.py
python3 Tests/SampCert-py/testing-kolmogorov-discretelaplace.py
```
The script reports `Test passed!` when the kolmogorov distance between the computed and ideal CDF is within `0.02`. 


## Tests: FFI samplers

To demonstrate our claim that our code can be executed within Lean using the C FFI we have rewritten the K-S test, as well as several example queries, inside the file `Test.lean`. 
To run that file, execute the command 
```
lake exe test
```

This will do the following:
- Execute our implementation of the sparse vector technique on randomly generated sample data 
- Execute our noised histogram query, and histogram mean queries, on randomly generated sample data,
- Preform stastical tests on our implementation of the discrete Gaussian, and report the Kolmogorov distance as above. 
