FROM --platform=linux/amd64 debian:trixie


#install general setup tools
RUN apt update -y
RUN apt install -y build-essential libc6 git emacs-nox wget

# Install miniconda & sympy & z3
RUN wget https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh
RUN bash ./Miniconda3-latest-Linux-x86_64.sh -b
# recent Miniconda requires explicitly accepting the default channels' Terms of Service
RUN /root/miniconda3/bin/conda tos accept --override-channels --channel https://repo.anaconda.com/pkgs/main
RUN /root/miniconda3/bin/conda tos accept --override-channels --channel https://repo.anaconda.com/pkgs/r
RUN /root/miniconda3/bin/conda install python=3.14 sympy pip -y
# z3-solver is pinned: invariant counts (ieq/congruence bounds) are z3-version
# sensitive, and tests/golden.json is generated against this exact version.
RUN /root/miniconda3/bin/pip3 install z3-solver==4.16.0.0 beartype pycparser numpy
# anthropic is only needed for the optional LLM mode (dig.py -llm); harmless otherwise
RUN /root/miniconda3/bin/pip3 install anthropic
RUN rm -rf ./Miniconda3-latest-Linux-x86_64.sh

WORKDIR /
COPY . /dig

WORKDIR /dig/src
