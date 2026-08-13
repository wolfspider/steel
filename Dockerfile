FROM ubuntu:latest

SHELL ["/bin/bash", "-c"]

# Base dependencies: opam
# CI dependencies: jq (to identify F* branch)
# python3 (for interactive tests)
# libicu (for .NET, cf. https://aka.ms/dotnet-missing-libicu )
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
      ca-certificates \
      curl \
      wget \
      git \
      gnupg \
      sudo \
      python3 \
      python-is-python3 \
      libicu-dev \
      libgmp-dev \
      pkg-config \
      time \
      opam \
      vim \
    && apt-get clean -y
# FIXME: libgmp-dev should be installed automatically by opam,
# but it is not working, so just adding it above.

# Create a new user and give them sudo rights
ARG USER=vscode
RUN useradd -d /home/$USER -s /bin/bash -m $USER
RUN echo "$USER ALL=NOPASSWD: ALL" >> /etc/sudoers
USER $USER
ENV HOME /home/$USER
WORKDIR $HOME
RUN mkdir -p $HOME/bin

# Make sure ~/bin is in the PATH
RUN echo 'export PATH=$HOME/bin:$PATH' | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile

# Install OCaml
ARG OCAML_VERSION=5.3.0
RUN opam init --compiler=$OCAML_VERSION --disable-sandboxing
RUN opam option depext-run-installs=true
ENV OPAMYES=1
RUN opam install --yes batteries zarith stdint yojson dune menhir menhirLib pprint sedlex ppxlib process ppx_deriving ppx_deriving_yojson memtrace mtime visitors uucp wasm fix eio eio_main ocamlformat

# Get compiled Z3
RUN wget -nv https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip \
 && unzip z3-4.13.3-x64-glibc-2.35.zip \
 && cp z3-4.13.3-x64-glibc-2.35/bin/z3 $HOME/bin/z3 \
 && rm -r z3-4.13.3-*

# Get F* master and build
RUN eval $(opam env) \
 && source $HOME/.profile \
 && git clone --depth=1 https://github.com/FStarLang/FStar \
 && cd FStar/ \
 && make ADMIT=1 \
 && ln -s $(realpath bin/fstar.exe) $HOME/bin/fstar.exe

# Get karamel master and build
RUN eval $(opam env) \
 && source $HOME/.profile \
 && git clone --depth=1 https://github.com/FStarLang/karamel \
 && cd karamel/ \
 && make

ENV FSTAR_HOME $HOME/FStar
ENV KRML_HOME $HOME/karamel

# Copy everything from current directory (build context) into /steel inside the image
# Copy everything and set ownership in one step
COPY --chown=${USER:-vscode}:${USER:-vscode} . /steel

# Set working directory
WORKDIR /steel

# Run make
RUN eval "$(opam env)" && source $HOME/.profile && make

# Instrument .bashrc to set the opam switch. Note that this
# just appends the *call* to eval $(opam env) in these files, so we
# compute the new environments fter the fact. Calling opam env here
# would perhaps thrash some variables set by the devcontainer infra.
RUN echo 'eval $(opam env --set-switch)' | tee --append $HOME/.bashrc


