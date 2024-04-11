FROM --platform=linux/amd64 debian:bookworm


#install general setup tools
RUN apt update -y
RUN apt install -y build-essential libc6 git software-properties-common emacs-nox wget openjdk-17-jdk

# Install miniconda & sympy & z3
RUN wget https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh
RUN bash ./Miniconda3-latest-Linux-x86_64.sh -b
RUN /root/miniconda3/bin/conda install sympy pip -y
RUN /root/miniconda3/bin/pip3 install z3-solver beartype pycparser
RUN rm -rf ./Miniconda3-latest-Linux-x86_64.sh

WORKDIR /
COPY . /dig

## CIVL and Goblint-Cil
WORKDIR /dig/EXTERNAL_FILES
RUN tar xf CIVL-1.22_5854.tgz ; ln -sf CIVL-1.22_5854/ civl
RUN cp dot_sarl ~/.sarl   # NEED TO MANUALLY PUT IN Z3 VERSION

WORKDIR /dig/src
