FROM debian:bullseye

COPY . /dig

#install sage and z3
RUN apt-get update -y
RUN apt-get install -y build-essential
RUN apt-get install -y sagemath
RUN apt-get install -y z3
RUN apt-get install -y git
RUN apt-get install -y ant
RUN pip install z3-solver

#download java and jpf
RUN apt-get install -y default-jdk
RUN mkdir /usr/lib/JPF
WORKDIR /usr/lib/JPF
RUN git clone https://github.com/javapathfinder/jpf-core
RUN git clone https://github.com/SymbolicPathFinder/jpf-symbc

#setup jpf env
RUN mkdir /root/.jpf
RUN echo 'jpf-core = /usr/lib/JPF/jpf-core' >> /root/.jpf/site.properties
RUN echo 'jpf-symbc = /usr/lib/JPF/jpf-symbc' >> /root/.jpf/site.properties
RUN echo 'extensions=${jpf-core},${jpf-symbc}' >> /root/.jpf/site.properties

#build jpf
WORKDIR /usr/lib/JPF/jpf-core
RUN git checkout java-8
RUN ant
RUN cp /dig/src/java/InvariantListenerVu.java /usr/lib/JPF/jpf-symbc/src/main/gov/nasa/jpf/symbc
WORKDIR /usr/lib/JPF/jpf-symbc
RUN ant

#build dig
WORKDIR /dig/src/java
RUN make

#setup path
ENV JPF_HOME=/usr/lib/JPF
ENV JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64/
ENV LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$JPF_HOME/jpf-symbc/lib

WORKDIR /dig/src
