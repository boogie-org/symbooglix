#!/bin/bash
set -e
set -x
set -o pipefail

: ${SBX_SRC?"SBX_SRC must be set"}
: ${BUILD_TYPE?"BUILD_TYPE must be set"}

cd "${SBX_SRC}"

# Run driver tests
lit -v --param sbx_build=${BUILD_TYPE} test_programs/

# Run unit tests
utils/run-unit-tests.sh ./testrunner/NUnit.Runners.2.6.4/tools/nunit-console.exe ${BUILD_TYPE}
