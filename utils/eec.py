#!/usr/bin/env python
"""
This simple script runs a program and returns 0
if the exit code was as expected, otherwise
it returns 255

e.g.
$ eec 0 true
$ eec 1 ls -l
"""
import sys
import subprocess

if __name__ == '__main__':
    if len(sys.argv) < 3:
       sys.stderr.write('Must pass at least 2 arguments\n')
       sys.exit(255)

    expectedExitCode = int(sys.argv[1])
    cmdLine = sys.argv[2:]
    p = subprocess.Popen(cmdLine)
    result = p.wait()

    if result == expectedExitCode:
        sys.exit(0)
    else:
        print("ERROR: Expected exit code {} but was {}".format(expectedExitCode, result))
        sys.exit(255)
