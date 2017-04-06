#!/bin/bash
set -o pipefail
set -e
: ${Z3_BIN?"Z3_BIN must be set"}
Z3_STDIN_LOG="z3_in_log.txt"
Z3_STDOUT_LOG="z3_out_log.txt"
Z3_STDERR_LOG="z3_stderr_log.txt"
tee --append ${Z3_STDIN_LOG} | ${Z3_BIN} "$@" 2>> "${Z3_STDERR_LOG}" | tee --append ${Z3_STDOUT_LOG}
