FROM debian:buster

#install general setup tools
RUN apt-get update -y
RUN apt-get install -y build-essential git software-properties-common emacs ocaml ocamlbuild ocaml-findlib wget openjdk-11-jdk unzip


# Install miniconda & sympy & z3
RUN wget https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh
RUN bash ./Miniconda3-latest-Linux-x86_64.sh -b
RUN /root/miniconda3/bin/conda install sympy pip -y  
RUN /root/miniconda3/bin/pip3 install z3-solver


# # # download Eclipse Foundation's AdoptOpenJDK build of jdk 8
# # RUN apt-get wget apt-transport-https gnupg -y
# # RUN wget -qO - https://adoptopenjdk.jfrog.io/adoptopenjdk/api/gpg/key/public | apt-key add -
# # RUN echo "deb https://adoptopenjdk.jfrog.io/adoptopenjdk/deb bullseye main" | tee /etc/apt/sources.list.d/adoptopenjdk.list
# # RUN apt-get update -y
# # RUN apt-get install adoptopenjdk-8-hotspot -y
# # RUN update-alternatives --set java /usr/lib/jvm/adoptopenjdk-8-hotspot-amd64/bin/java


WORKDIR /
COPY . /dig

## Ocaml and CIL for C code instrumentation
WORKDIR /dig/EXTERNAL_FILES
RUN unzip develop.zip && mv cil-develop cil
WORKDIR cil
RUN ./configure && make

WORKDIR /dig/src/ocaml
RUN make clean; make

## CIVL
WORKDIR /dig/EXTERNAL_FILES
RUN tar xf CIVL-1.20_5259.tgz ; ln -sf CIVL-1.20_5259 civl ; ln -sf civl/lib/ lib
RUN cp dot_sarl ~/.sarl


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









WORKDIR /dig/src
