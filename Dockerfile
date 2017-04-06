FROM ubuntu:14.04
MAINTAINER Dan Liew <daniel.liew@imperial.ac.uk>

ENV CONTAINER_USER=sbx \
    BUILD_TYPE=Release \
    MONO_VERSION=4.8.0 \
    SBX_SRC=/home/sbx/symbooglix \
    SKIP_SUBMODULE_SETUP=1

# FIXME: This is overkill, we don't need everything from mono.
# Note ca-certificates-mono is needed so NuGet can pull down the packages we need.
RUN apt-get update && apt-get -y install wget && \
    wget -O - http://download.mono-project.com/repo/xamarin.gpg |apt-key add - && \
    echo "deb http://download.mono-project.com/repo/debian wheezy/snapshots/${MONO_VERSION} main" > /etc/apt/sources.list.d/mono-xamarin.list && \
    wget -O - http://download.opensuse.org/repositories/home:delcypher:z3/xUbuntu_14.04/Release.key | apt-key add - && \
    echo 'deb http://download.opensuse.org/repositories/home:/delcypher:/z3/xUbuntu_14.04/ /' >> /etc/apt/sources.list.d/smt.list && \
    apt-get update && \
    apt-get -y install --no-install-recommends mono-devel ca-certificates-mono z3=4.4.1-0

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
RUN apt-get -y --no-install-recommends install python3 python3-pip libyaml-dev && \
    update-alternatives --install /usr/bin/python python /usr/bin/python3 10 && \
    update-alternatives --install /usr/bin/pip pip /usr/bin/pip3 10 && \
    apt-get -y install python3-dev && \
    pip install psutil pyyaml lit OutputCheck && \
    apt-get remove -y python3-dev && apt-get autoremove -y


# Copy across the sources.
# This assumes that the git submodules have been initialised
RUN mkdir -p ${SBX_SRC}
ADD README.md ${SBX_SRC}/
ADD ExternalLibs ${SBX_SRC}/ExternalLibs/
ADD src ${SBX_SRC}/src
ADD test_programs ${SBX_SRC}/test_programs
ADD utils ${SBX_SRC}/utils
RUN chown --recursive ${CONTAINER_USER} ${SBX_SRC}

# Switch to container user and build
USER ${CONTAINER_USER}
RUN cd ${SBX_SRC} && \
    utils/travis-prepare.sh && \
    utils/travis-build.sh

# Put sbx.exe in the user's PATH
RUN echo 'export PATH=$PATH:${SBX_SRC}/src/SymbooglixDriver/bin/${BUILD_TYPE}' >> \
    /home/${CONTAINER_USER}/.bashrc

# TODO: Run tests in container
