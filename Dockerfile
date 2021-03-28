FROM debian:bullseye

COPY . /dig

#install general setup tools
RUN apt-get update -y
RUN apt-get install -y build-essential git ant

#download Eclipse Foundation's AdoptOpenJDK build of jdk 8
RUN apt-get install wget apt-transport-https gnupg -y
RUN wget -qO - https://adoptopenjdk.jfrog.io/adoptopenjdk/api/gpg/key/public | apt-key add -
RUN echo "deb https://adoptopenjdk.jfrog.io/adoptopenjdk/deb bullseye main" | tee /etc/apt/sources.list.d/adoptopenjdk.list
RUN apt-get update -y
RUN apt-get install adoptopenjdk-8-hotspot -y
RUN update-alternatives --set java /usr/lib/jvm/adoptopenjdk-8-hotspot-amd64/bin/java

#download java and jpf
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

RUN apt-get install -y sagemath z3 
RUN pip install z3-solver

#build dig
WORKDIR /dig/src/java
RUN make

#setup path
ENV JPF_HOME=/usr/lib/JPF
ENV JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64/
ENV LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$JPF_HOME/jpf-symbc/lib
ENV JAVA8_HOME=/usr/lib/jvm/adoptopenjdk-8-hotspot-amd64/

WORKDIR /dig/src
