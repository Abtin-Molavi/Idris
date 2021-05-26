FROM ubuntu:18.04
RUN apt update
RUN apt install make
# haskell 
RUN apt install -y haskell-platform

# gmp 
RUN apt install -y wget
RUN apt install -y m4
WORKDIR /home/tools/
RUN wget https://gmplib.org/download/gmp/gmp-6.0.0a.tar.bz2
RUN bzip2 -d gmp-6.0.0a.tar.bz2
RUN tar -xof gmp-6.0.0a.tar
WORKDIR /home/tools/gmp-6.0.0
RUN ./configure
RUN make && make check && make install

# Idris
RUN cabal update && cabal install idris
ENV PATH="/root/.cabal/bin/:${PATH}"