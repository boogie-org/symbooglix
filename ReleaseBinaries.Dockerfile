FROM ubuntu:14.04
MAINTAINER Dan Liew <daniel.liew@imperial.ac.uk>

ENV CONTAINER_USER=sbx \
    BINARY_DIR=src/SymbooglixDriver/bin/Release

# Get Mono 3.12.1 . Perhaps we should build it ourselves
# because we had to patch it to avoid crashes when calling
# System.Environment.Exit()
#
# See https://github.com/mono/mono/pull/1649
# FIXME: This is overkill, we don't need everything from mono
RUN apt-get update && apt-get -y install wget && \
    wget -O - http://download.mono-project.com/repo/xamarin.gpg |apt-key add - && \
    echo "deb http://download.mono-project.com/repo/debian wheezy/snapshots/3.12.0 main" > /etc/apt/sources.list.d/mono-xamarin.list && \
    apt-key adv --recv-keys --keyserver keyserver.ubuntu.com C504E590 && \
    echo 'deb http://ppa.launchpad.net/delcypher/boogaloo-smt/ubuntu trusty main' > /etc/apt/sources.list.d/smt.list && \
    apt-get update && \
    apt-get -y install mono-complete z3=4.3.1-0~trusty1

# Create ``sbx`` user for container with password ``sbx``.
# Give it sudo access so it possible to install new packages inside the container.
# NEVER EVER EVER EVER USE THIS CONTAINER IN PRODUCTION DUE HOW EASY IT IS
# TO GET ROOT PRIVILIDGES WITH THE ``sbx`` USER!
RUN useradd -m ${CONTAINER_USER} && \
    echo ${CONTAINER_USER}:${CONTAINER_USER} | chpasswd && \
    echo "${CONTAINER_USER}  ALL=(root) ALL" >> /etc/sudoers

WORKDIR /home/${CONTAINER_USER}/

# Copy across the Release Binaries
RUN mkdir /home/${CONTAINER_USER}/symbooglix/
ADD ${BINARY_DIR}/*.dll /home/${CONTAINER_USER}/symbooglix/
ADD ${BINARY_DIR}/*.exe /home/${CONTAINER_USER}/symbooglix/
RUN ln -s /usr/bin/z3 /home/${CONTAINER_USER}/symbooglix/z3.exe

# FIX the ownership of the binaries
RUN chown -R ${CONTAINER_USER}: /home/${CONTAINER_USER}/symbooglix

USER ${CONTAINER_USER}

# Put sbx.exe in the user's PATH
RUN echo 'export PATH=$PATH:/home/${CONTAINER_USER}/symbooglix' >> \
    /home/${CONTAINER_USER}/.bashrc
