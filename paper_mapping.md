## Reference from the paper to the code

| §    | Kind        | Item from paper                                    | File                                                                      | Name                                     | Note       |
|------|-------------|----------------------------------------------------|---------------------------------------------------------------------------|------------------------------------------|------------|
| 1    | Folder      | Library of DP mechanisms                           | [SampCert/DifferentialPrivacy/Queries/]                                   |                                          |            |
|      | Folder      | Sampling algorithms                                | [SampCert/Samplers/]                                                      |                                          |            |
|      | Folder      | Pure DP Instantiation                              | [SampCert/DifferentialPrivacy/Pure]                                       |                                          |            |
|      | Folder      | zCDP Instantiation                                 | [SampCert/DifferentialPrivacy/ZeroConcentrated]                           |                                          |            |
| 2    | Definition  | Query                                              | [SampCert/DifferentialPrivacy/Generic.lean]                               | `Query`                                  |            |
|      | Definition  | Mechanism                                          | [SampCert/DifferentialPrivacy/Generic.lean]                               | `Mechanism`                              |            |
|      | Definition  | Neighbour                                          | [SampCert/DifferentialPrivacy/Neighbours.lean]                            | `Neighbour`                              |            |
|      | Definition  | `AbstractDP`                                       | [SampCert/DifferentialPrivacy/Abstract.lean]                              | `DPSystem`                               | Listing 1  |
|      | Definition  | `privComposeAdaptive`                              | [SampCert/DifferentialPrivacy/Generic.lean]                               | `privComposeAdaptive`                    |            |
|      | Definition  | `privPostProcess`                                  | [SampCert/DifferentialPrivacy/Generic.lean]                               | `privPostProcess`                        |            |
|      | Definition  | `privConst`                                        | [SampCert/DifferentialPrivacy/Generic.lean]                               | `privConst`                              |            |
|      | Definition  | `DPNoise`                                          | [SampCert/DifferentialPrivacy/Abstract.lean]                              | `DPNoise`                                | Listing 2  |
|      | Definition  | `ApproximateDP`                                    | [SampCert/DifferentialPrivacy/Approximate/DP.lean]                        | `ApproximateDP`                          |            |
|      | Definition  | Sensitivity                                        | [SampCert/DifferentialPrivacy/Sensitivity.lean]                           | `sensitivity`                            |            |
|      | Example     | Private histogram                                  | [SampCert/DifferentialPrivacy/Queries/Histogram/]                         |                                          |            |
|      | Definition  | Private histogram implementation                   | [SampCert/DifferentialPrivacy/Queries/Histogram/Code.lean]                |                                          | Listing 3  |
|      | Definition  | Private histogram  `Bins`                          | [SampCert/DifferentialPrivacy/Queries/Histogram/Code.lean]                | `Bins`                                   |            |
|      | Definition  | Private histogram  `Histogram`                     | [SampCert/DifferentialPrivacy/Queries/Histogram/Code.lean]                | `Histogram`                              |            |
|      | Lemma       | Noised count ADP                                   | [SampCert/DifferentialPrivacy/Queries/Histogram/Properties.lean]          | `privNoisedBinCount_DP`                  | Listing 4  |
|      | Lemma       | Noised histogram aux ADP                           | [SampCert/DifferentialPrivacy/Queries/Histogram/Properties.lean]          | `privNoisedHistogramAux_DP`              | Listing 5  |
|      | Lemma       | Private histogram ADP                              | [SampCert/DifferentialPrivacy/Queries/Histogram/Properties.lean]          | `privNoisedHistogram_DP`                 | Listing 6  |
|      | Definition  | Pure DP                                            | [SampCert/DifferentialPrivacy/Pure/DP.lean]                               | `pureDP`                                 |            |
|      | Definition  | Discrete Laplace mechanism                         | [SampCert/DifferentialPrivacy/Pure/Mechanism/Code.lean]                   | `privNoisedQueryPure`                    |            |
|      | Lemma       | Pure DP of discrete Laplace mechanism              | [SampCert/DifferentialPrivacy/Pure/Mechanism/Properties.lean]             | `privNoisedQueryPure_DP`                 |            |
|      | Lemma       | Pure DP adaptive composition bound                 | [SampCert/DifferentialPrivacy/Pure/AdaptiveComposition.lean]              | `PureDP_ComposeAdaptive'`                |            |
|      | Lemma       | Pure DP postprocessing bound                       | [SampCert/DifferentialPrivacy/Pure/Postprocessing.lean]                   | `PureDP_PostProcess`                     |            |
|      | Lemma       | Pure DP implies approximate DP                     | [SampCert/DifferentialPrivacy/Pure/DP.lean]                               | `pure_ApproximateDP`                     |            |
|      | Instance    | `AbstractDP` instance for Pure DP                  | [SampCert/DifferentialPrivacy/Pure/System.lean]                           | `PureDPSystem`                           |            |
|      | Instance    | `DPNoise` instance for Pure DP                     | [SampCert/DifferentialPrivacy/Pure/System.lean]                           | `laplace_pureDPSystem`                   |            |
|      | Definition  | Zero-concentrated DP                               | [SampCert/DifferentialPrivacy/ZeroConcentrated/DP.lean]                   | `zCDP`                                   |            |
|      | Definition  | Discrete Gaussian mechanism                        | [SampCert/DifferentialPrivacy/ZeroConcentrated/Mechanism/Code.lean]       | `privNoisedQuery`                        |            |
|      | Lemma       | zCDP of discrete Gaussian mechanism                | [SampCert/DifferentialPrivacy/ZeroConcentrated/Mechanism/Properties.lean] | `privNoisedQuery_zCDP`                   |            |
|      | Lemma       | zCDP adaptive composition bound                    | [SampCert/DifferentialPrivacy/ZeroConcentrated/AdaptiveComposition.lean]  | `privComposeAdaptive_zCDP `              |            |
|      | Lemma       | zCDP postprocessing bound                          | [SampCert/DifferentialPrivacy/ZeroConcentrated/Postprocessing.lean]       | `privPostProcess_zCDP`                   |            |
|      | Lemma       | zCDP implies approximate DP                        | [SampCert/DifferentialPrivacy/ZeroConcentrated/DP.lean]                   | `zCDP_ApproximateDP`                     |            |
|      | Instance    | `AbstractDP` instance for zCDP                     | [SampCert/DifferentialPrivacy/ZeroConcentrated/System.lean]               | `zCDPSystem`                             |            |
|      | Instance    | `DPNoise` instance for zCDP                        | [SampCert/DifferentialPrivacy/ZeroConcentrated/System.lean]               | `gaussian_zCDPSystem`                    |            |
| 3    | Definition  | SLang primitives                                   | [SampCert/SLang.lean]                                                     |                                          | Figure 3   |
|      | Definition  | Geometric sampler                                  | [SampCert/Samplers/Geometric/Code.lean]                                   | `probGeometric`                          |            |
|      | Lemma       | Geometric sampler correctness proof                | [SampCert/Samplers/Geometric/Properties.lean]                             | `probGeometric_apply`                    |            |
|      | Lemma       | Geometric sampler normalization proof              | [SampCert/Samplers/Geometric/Properties.lean]                             | `probGeometric_normalizes`               |            |
|      | Definition  | Laplace sampler                                    | [SampCert/Samplers/Laplace/Code.lean]                                     | `DiscreteLaplaceSample`                  | Listing 8  |
|      | Definition  | Optimized Laplace sampler                          | [SampCert/Samplers/Laplace/Code.lean]                                     | `DiscreteLaplaceOptimized`               | Listing 9  |
|      | Definition  | Dynamically switching Laplace sampler              | [SampCert/Samplers/Laplace/Code.lean]                                     | `DiscreteLaplaceSampleMixed`             |            |
|      | Lemma       | Laplace sampler correctness proof                  | [SampCert/Samplers/Laplace/Properties.lean]                               | `DiscreteLaplaceSample_apply`            |            |
|      | Lemma       | Laplace sampler equivalences                       | [SampCert/Samplers/Laplace/Properties.lean]                               | `DiscreteLaplaceSample_equiv`            |            |
|      | Lemma       | Laplace sampler normalizes                         | [SampCert/Samplers/Laplace/Properties.lean]                               | `DiscreteLaplaceSampleMixed_normalizes ` |            |
|      | Definition  | Discrete Gaussian sampler                          | [SampCert/Samplers/Gaussian/Code.lean]                                    | `DiscreteGaussianSample`                 | Listing 10 |
|      | Definition  | Discrete Gaussian correctness                      | [SampCert/Samplers/Gaussian/Properties.lean]                              | `DiscreteGaussianSample_apply`           |            |
|      | Definition  | Discrete Gaussian normalizes                       | [SampCert/Samplers/Gaussian/Properties.lean]                              | `DiscreteGaussianSample_normalizes`      |            |
| 4    | C++ Program | SLang FFI implementations                          | [ffi.cpp]                                                                 |                                          | Listing 11 |
| Misc | Definition  | Generic parallel composition                       | [SampCert/DifferentialPrivacy/Generic.lean]                               | `privParComp`                            |            |
|      | Lemma       | Parallel composition typeclass                     | [SampCert/DifferentialPrivacy/Abstract.lean]                              | `DPPar`                                  |            |
|      | Definition  | `DPPar` instance for Pure DP                       | [SampCert/DifferentialPrivacy/Pure/System.lean]                           | `PureDPParSystem`                        |            |
|      | Folder      | Sparse Vector Technique                            | [SampCert/DifferentialPrivacy/UnboundedMax/]                              |                                          |            |
|      | Definition  | Sparse Vector Technique, executable implementation | [SampCert/DifferentialPrivacy/UnboundedMax/Code.lean]                     | `sv1_privMax`                            |            |
|      | Definition  | Sparse Vector Technique, private form              | [SampCert/DifferentialPrivacy/UnboundedMax/Properties.lean]               | `sv9_privMax`                            |            |
|      | Definition  | Sparse Vector Technique, SPMF                      | [SampCert/DifferentialPrivacy/UnboundedMax/Properties.lean]               | `sv1_privMax_PMF`                        |            |
|      | Lemma       | Sparse Vector Technique pure DP                    | [SampCert/DifferentialPrivacy/UnboundedMax/Privacy.lean]                  | `sv9_privMax_pmf_DP`                     |            |
|      | Lemma       | DP implies zCDP                                    | [SampCert/DifferentialPrivacy/ZeroConcentrated/DP.lean]                   | `ofDP`                                   |            |



