#!/bin/bash
set -e
set -x
set -o pipefail

: ${SBX_SRC?"SBX_SRC must be set"}
: ${BUILD_TYPE?"BUILD_TYPE must be set"}
TRAVIS_SOLUTION=${TRAVIS_SOLUTION:-${SBX_SRC}/src/Symbooglix.sln}
NUGET_URL=${NUGET_URL:-https://dist.nuget.org/win-x86-commandline/v2.8.6/nuget.exe}

cd "${SBX_SRC}"

if [ -n "${TRAVIS}" ]; then
  NUGET=("nuget")
else
  # Get NuGet
  wget ${NUGET_URL} -O nuget.exe
  NUGET=(mono "${SBX_SRC}/nuget.exe")
fi

# Restore packages
${NUGET[*]} restore ${TRAVIS_SOLUTION}

# Download NUnit runners
${NUGET[*]} install NUnit.Runners -Version 2.6.4 -OutputDirectory testrunner

# Set up git submodules
if [ "X${SKIP_SUBMODULE_SETUP}" != "X1" ]; then
  git submodule init
  git submodule update
fi

