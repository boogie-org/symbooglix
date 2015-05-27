FROM ubuntu:14.04
MAINTAINER Dan Liew <daniel.liew@imperial.ac.uk>

ENV CONTAINER_USER=ase \
    BINARY_DIR=src/SymbooglixDriver/bin/Release \
    BOOGIE_RUNNER_REVISION=9be74e6e12bac25befa0f4fb13ced040754b702a

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
    apt-get -y install --no-install-recommends mono-devel z3=4.3.1-0~trusty1

# Create user for container with password set to the user name
# Give it sudo access so it possible to install new packages inside the container.
# NEVER EVER EVER EVER USE THIS CONTAINER IN PRODUCTION DUE HOW EASY IT IS
# TO GET ROOT PRIVILIDGES WITH THE ${CONTAINER_USER} USER!
RUN useradd -m ${CONTAINER_USER} && \
    echo ${CONTAINER_USER}:${CONTAINER_USER} | chpasswd && \
    echo "${CONTAINER_USER}  ALL=(root) ALL" >> /etc/sudoers

WORKDIR /home/${CONTAINER_USER}/

# Setup Python
# Note python3-dev installs gcc. We need that so pyyaml gets built properly
# but remove gcc (and other bits) afterwards to save space
RUN apt-get -y --no-install-recommends install python3 python3-pip libyaml-dev git && \
    update-alternatives --install /usr/bin/python python /usr/bin/python3 10 && \
    update-alternatives --install /usr/bin/pip pip /usr/bin/pip3 10 && \
    apt-get -y install python3-dev && \
    pip install psutil pyyaml && \
    apt-get remove -y python3-dev && apt-get autoremove -y


# Copy across the Release Binaries
RUN mkdir /home/${CONTAINER_USER}/symbooglix/
ADD ${BINARY_DIR}/*.dll /home/${CONTAINER_USER}/symbooglix/
ADD ${BINARY_DIR}/*.exe /home/${CONTAINER_USER}/symbooglix/
RUN ln -s /usr/bin/z3 /home/${CONTAINER_USER}/symbooglix/z3.exe

# FIX the ownership of the binaries
RUN chown -R ${CONTAINER_USER}: /home/${CONTAINER_USER}/symbooglix

# Copy across boogie-runner configs
ADD symbooglix-svcomp.yml symbooglix-gpu.yml /home/${CONTAINER_USER}/
RUN chown ${CONTAINER_USER}: *.yml

USER ${CONTAINER_USER}

# Put sbx.exe in the user's PATH
RUN echo 'export PATH=$PATH:/home/${CONTAINER_USER}/symbooglix' >> \
    /home/${CONTAINER_USER}/.bashrc

# Install boogie-runner
RUN git clone https://github.com/symbooglix/boogie-runner.git && \
    cd boogie-runner && \
    git checkout ${BOOGIE_RUNNER_REVISION} && \
    echo 'PATH=/home/${CONTAINER_USER}/boogie-runner:$PATH' >> \
         /home/${CONTAINER_USER}/.bashrc
