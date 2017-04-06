#!/bin/bash
# This is hacky script to run all the unit tests

function usage() {
  echo "$0 [options] <CONSOLE_RUNNER_PATH> <BUILD_TYPE>"
  echo ""
  echo "OPTIONS"
  echo "-h --help - Show help information"
  echo "--stop-on-error - Stop on first test failure"
  echo "--unit-tests=* - Run only these sets of tests"
}

STOP_ON_ERROR=0
CONSOLE_RUNNER=""
BUILD_TYPE=""
# In msec
TIMEOUT=300000

DEFAULT_UNIT_TESTS=(ExprBuilderTests BoogieTests SymbooglixLibTests)
UNIT_TESTS=()
EXTRA_RUNNER_ARGS=()
while [ $# -gt 2 -o "$1" = "--help" -o "$1" = "-h" ]; do
  case "$1" in
    -h | --help)
      usage
      exit 0
    ;;
    --stop-on-error)
      EXTRA_RUNNER_ARGS+=('-stoponerror')
      ;;
    --unit-tests=*)
      for t in $(echo "$1" | sed -e 's/--unit-tests=//' -e 's/,/ /g'); do
        echo "Adding test suite $t"
        UNIT_TESTS+=("$t")
      done
      ;;
    *)
      echo "Unrecognised option \"$1\""
      exit 1
      ;;
  esac
  shift
done

if [ $# -ne 2 ]; then
  echo "Insufficient number of argument. See --help"
  exit 1
fi

CONSOLE_RUNNER="$1"
BUILD_TYPE="$2"

if [ -z "${CONSOLE_RUNNER}" ]; then
  echo "CONSOLE_RUNNER not specified"
  exit 1
fi
if [ -z "${BUILD_TYPE}" ]; then
  echo "BUILD_TYPE not specified"
  exit 1
fi

if [ ${#UNIT_TESTS[@]} -eq 0 ]; then
  echo "Using default unit tests"
  UNIT_TESTS=(${DEFAULT_UNIT_TESTS[@]})
fi
echo "Using unit tests ${UNIT_TESTS[@]}"

REPO_ROOT=$( cd ${BASH_SOURCE[0]%/*}/../ ; echo "$PWD" )

set -x
for test in ${UNIT_TESTS[@]} ; do
    echo "Running suite ${test}"
    mono --debug ${CONSOLE_RUNNER} \
        -nologo \
        -output=temp.out \
        -err=temp.err \
        "${EXTRA_RUNNER_ARGS[@]}" \
        -timeout=${TIMEOUT} \
        ${REPO_ROOT}/src/${test}/bin/${BUILD_TYPE}/${test}.dll

    if [ $? -ne 0 ]; then
        echo "Failure"
        exit 1
    fi

    rm -f temp.out
    rm -f temp.err
done
