FROM --platform=linux/amd64 debian:bookworm


#install general setup tools
RUN apt update -y
RUN apt install -y build-essential libc6 git software-properties-common emacs-nox wget

# Install miniconda & sympy & z3
RUN wget https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh
RUN bash ./Miniconda3-latest-Linux-x86_64.sh -b
RUN /root/miniconda3/bin/conda install python=3.14 sympy pip -y
RUN /root/miniconda3/bin/pip3 install z3-solver beartype pycparser numpy
# anthropic is only needed for the optional LLM mode (dig.py -llm); harmless otherwise
RUN /root/miniconda3/bin/pip3 install anthropic
RUN rm -rf ./Miniconda3-latest-Linux-x86_64.sh

WORKDIR /
COPY . /dig

WORKDIR /dig/src
