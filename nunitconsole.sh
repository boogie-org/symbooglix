#!/bin/bash

# This is a script that wraps invocation of nunit-console4 that creates a copy
# of the .csproj pointed to and fixes the paths so they don't have mixed UNIX
# and windows path slashes which currently happens with the NUnit console
# which causes System.IO.DirectoryNotFoundException

if [ $# -eq 0 ]; then
    echo "You must specify at least one argument"
    exit 1
fi

if [ "${1}" == "-help" ]; then
    nunit-console4 -help
    exit 0
fi

CSPROJ="${1}"

if [ ! -e "${CSPROJ}" ]; then
    echo "${CSPROJ} does not exist"
    exit 1
fi

if [ "${CSPROJ##*.}" != "csproj" ]; then
    echo "${CSPROJ} is not a .csproj file"
    exit 1
fi

# Make a copy
COPY="${CSPROJ}.hacked_copy.csproj"
sed -s 's#bin\\#bin/#g' "${CSPROJ}" > "${COPY}"

nunit-console4 "${COPY}" ${@:2}
rm "${COPY}"
