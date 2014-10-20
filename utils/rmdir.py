#!/usr/bin/python
"""
This script is a convenient script for removing a directory and its contents.
On POSIX operating systems we can just use ``rm -rf`` but that doesn't work on
Windows and there isn't an equivalent on Windows that will exit with a zero
exit code if the directory does not exist.
"""
import argparse
import logging
import os
import shutil
import sys

def main(args):
    logging.basicConfig(level=logging.DEBUG)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directories', nargs='+')

    parsedArgs = parser.parse_args(args)

    for directory in parsedArgs.directories:
        if not os.path.exists(directory):
            logging.info("'{}' does not exist. Skipping".format(directory))
            continue
        elif not os.path.isdir(directory):
            logging.info("'{}' is not a directory. Skipping".format(directory))
            continue

        logging.info("Removing directory '{}'".format(directory))
        shutil.rmtree(directory, ignore_errors=True)

    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))

