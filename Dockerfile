FROM xtrm0/dafny

USER root

RUN apt-get update && apt-get install curl git g++ vim python3-pip -y && apt-get clean

RUN pip install matplotlib scipy tqdm diffprivlib

# create a non-root user
RUN useradd -m lean

USER lean

WORKDIR /home/lean

SHELL ["/bin/bash", "-c"]

ENV PATH="/home/lean/.elan/bin:/home/lean/.local/bin:$PATH"

RUN mkdir SampCert

COPY --chown=lean . ./SampCert/

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none && \
    . ~/.profile && \
    elan toolchain install $(curl https://raw.githubusercontent.com/leanprover-community/mathlib/master/leanpkg.toml | grep lean_version | awk -F'"' '{print $2}') && \
    elan default stable

RUN cd SampCert/ && \
    lake exe cache get

RUN cd SampCert/ && \
    lake build

RUN cd SampCert/ && \
    lake build FastExtract && \
    dafny build --target:py Tests/SampCert.dfy Tests/Random.py Tests/testing-kolmogorov-discretegaussian.py Tests/testing-kolmogorov-discretelaplace.py Tests/IBM/discretegauss.py Tests/benchmarks.py -o Tests/SampCert.dfy

RUN cd SampCert && \
    lake build test
