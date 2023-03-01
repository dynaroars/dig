FROM debian:bullseye

#install general setup tools
RUN apt-get update -y
RUN apt-get install -y build-essential git software-properties-common emacs  wget openjdk-11-jdk unzip 

# ocaml ocamlbuild ocaml-findlib dune libppx-deriving-yojson-ocaml-dev libdune-ocaml-dev libzarith-ocaml-dev libyojson-ocaml-dev cppo

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
RUN tar xf CIVL-1.21_5476.tgz ; ln -sf CIVL-1.21_5476/ civl 
RUN cp dot_sarl ~/.sarl   # NEED TO MANUALLY PUT IN Z3 VERSION


## Ocaml and CIL for C code instrumentation
# RUN tar xf goblint-cil-2.0.1.tbz
# WORKDIR /dig/EXTERNAL_FILES/goblint-cil-2.0.1
# RUN dune build
# RUN dune build @install
# RUN dune install

# WORKDIR /dig/src/ocaml
# RUN make clean; make

WORKDIR /dig/src


## now can run DIG on trace files
## /root/miniconda3/bin/python3  dig.py ../tests/traces/cohendiv.csv
## DIG results ...

# running DIG on C files










# #download java and jpf
# # RUN mkdir /usr/lib/JPF
# # WORKDIR /usr/lib/JPF
# # RUN git clone https://github.com/javapathfinder/jpf-core
# # RUN git clone https://github.com/SymbolicPathFinder/jpf-symbc

# #setup jpf env
# # RUN mkdir /root/.jpf
# # RUN echo 'jpf-core = /usr/lib/JPF/jpf-core' >> /root/.jpf/site.properties
# # RUN echo 'jpf-symbc = /usr/lib/JPF/jpf-symbc' >> /root/.jpf/site.properties
# # RUN echo 'extensions=${jpf-core},${jpf-symbc}' >> /root/.jpf/site.properties

# #build jpf
# # WORKDIR /usr/lib/JPF/jpf-core
# # RUN git checkout java-8
# # RUN ant
# # RUN cp /dig/src/java/InvariantListenerVu.java /usr/lib/JPF/jpf-symbc/src/main/gov/nasa/jpf/symbc
# # WORKDIR /usr/lib/JPF/jpf-symbc
# # RUN ant

# # RUN apt-get install -y sagemath z3 
# # RUN pip install z3-solver

# #build dig
# # WORKDIR /dig/src/java
# # RUN make

# #setup path
# # ENV JPF_HOME=/usr/lib/JPF
# # ENV JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64/
# # ENV LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$JPF_HOME/jpf-symbc/lib
# # ENV JAVA8_HOME=/usr/lib/jvm/adoptopenjdk-8-hotspot-amd64/



# RUN mkdir CIL
# WORKDIR CIL
# # RUN apt-get install -y libzarith-ocaml-dev libbatteries-ocaml-dev libyojson-ocaml-dev libppx-deriving-yojson-ocaml-dev
# # RUN wget https://github.com/goblint/cil/archive/refs/tags/1.8.0.tar.gz
# # RUN tar xf 1.8.0.tar.gz
# # WORKDIR cil-1.8.0/
# RUN pwd
# RUN ./configure
# RUN make










# # # download AdoptOpenJDK build of jdk 8
# # RUN apt-get wget apt-transport-https gnupg -y
# # RUN wget -qO - https://adoptopenjdk.jfrog.io/adoptopenjdk/api/gpg/key/public | apt-key add -
# # RUN echo "deb https://adoptopenjdk.jfrog.io/adoptopenjdk/deb bullseye main" | tee /etc/apt/sources.list.d/adoptopenjdk.list
# # RUN apt-get update -y
# # RUN apt-get install adoptopenjdk-8-hotspot -y
# # RUN update-alternatives --set java /usr/lib/jvm/adoptopenjdk-8-hotspot-amd64/bin/java

