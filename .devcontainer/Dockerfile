FROM ubuntu

WORKDIR /root

ENV DEBIAN_FRONTEND=noninteractive \
    PATH=${PATH}:/root/.pack/bin

RUN apt-get update -y \
  && apt-get install -y \
  build-essential \
  curl \
  git \
  libgmp3-dev \
  libncurses5-dev \
  libncursesw5-dev \
  libx11-dev \
  rlwrap \
  && rm -rf /var/lib/apt/lists/

RUN git clone https://github.com/cisco/ChezScheme \
  && cd ChezScheme \
  && git checkout 1624184380340aa51404406439f15c75a4d67c4f \
  && ./configure --threads \
  && make \
  && make install \
  && cd .. \
  && rm -rf ChezScheme

RUN git clone https://github.com/stefan-hoeck/idris2-pack.git pack \
  && cd pack \
  && git checkout bb0cdc067da0d8be7922e7eb016c3fccd93059cb \
  && echo scheme | bash -c ./install.bash \
  && cd .. \
  && rm -rf pack

RUN yes yes | pack install-app idris2-lsp

