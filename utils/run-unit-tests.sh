#!/bin/bash
# This is hacky script to run all the unit tests

if [ $# -ne 2 ]; then
    echo "$0 <CONSOLE_RUNNER_PATH> <BUILD_TYPE>"
    exit 1
fi
CONSOLE_RUNNER="$1"
BUILD="$2"

# In msec
TIMEOUT=300000

REPO_ROOT=$( cd ${BASH_SOURCE[0]%/*}/../ ; echo "$PWD" )

UNIT_TESTS=(ExprBuilderTests BoogieTests SymbooglixLibTests)

for test in ${UNIT_TESTS[@]} ; do
    echo "Running suite ${test}"
    mono --debug ${CONSOLE_RUNNER} \
        -nologo \
        -nodots \
        -output=temp.out \
        -err=temp.err \
        -timeout=${TIMEOUT} \
        ${REPO_ROOT}/src/${test}/bin/${BUILD}/${test}.dll

    if [ $? -ne 0 ]; then
        echo "Failure"
        exit 1
    fi

    rm -f temp.out
    rm -f temp.err
done
