#!/bin/bash
set -e
set -x
set -o pipefail

: ${SBX_SRC?"SBX_SRC must be set"}
: ${BUILD_TYPE?"BUILD_TYPE must be set"}
TRAVIS_SOLUTION=${TRAVIS_SOLUTION:-${SBX_SRC}/src/Symbooglix.sln}
Z3_BIN=${Z3_BIN:-/usr/bin/z3}

cd "${SBX_SRC}"
xbuild /p:Configuration=${BUILD_TYPE} ${TRAVIS_SOLUTION}

# Setup symlinks for solver
Z3_PATHS=( \
  "src/SymbooglixDriver/bin/${BUILD_TYPE}/z3.exe" \
  "src/Symbooglix/bin/${BUILD_TYPE}/z3.exe" \
)
if [ "X${SKIP_Z3_SYMLINK_SETUP}" != "X1" ]; then
  for z3_path in ${Z3_PATHS[*]}; do
    rm -f "${z3_path}"
    ln -s ${Z3_BIN} "${z3_path}"
  done
fi
