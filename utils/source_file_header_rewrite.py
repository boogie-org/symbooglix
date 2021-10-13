#!/usr/bin/env python
"""
Simple utility for rewriting the headers in source files.
"""
import logging
import os
import re
import sys

new_header = """
//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2017 Daniel Liew
//
// This file is licensed under the MIT license.
// See LICENSE.txt for details.
//------------------------------------------------------------------------------
"""

# strip first \n
new_header = new_header[1:]

def add_header(output_lines):
  logging.debug('Adding header')
  for line in new_header.splitlines(keepends=True):
    logging.debug(f'Appending line: {repr(line)}')
    output_lines.append(line)

def process(file_path):
  output_lines = []
  # `\ufeff` is the byte-order-mark that is unfortunately
  # present in some of the source files.
  strip_region_re = re.compile('^(\ufeff)?' + r'//--')
  with open(file_path, 'r') as f:
    in_strip_region = False
    for idx, line in enumerate(f.readlines()):
      line_num = idx +1
      logging.debug(f'process line {line_num}: {repr(line)}')
      if in_strip_region is False:
        if strip_region_re.match(line):
          in_strip_region = True
          logging.debug(f'Entering strip region on line {line_num}')
          continue
      if in_strip_region is True:
        if strip_region_re.match(line):
          # Region ended
          logging.debug(f'Leaving strip region on line {line_num}')
          in_strip_region = None
          add_header(output_lines)
          continue
        # In strip region
        logging.debug(f'Dropping line {line_num}')
        continue
      # Outside of strip region
      logging.debug(f'Keeping line {line_num}')
      output_lines.append(line)

    with open(file_path, 'w') as f:
      for new_line in output_lines:
        f.write(new_line)


def main():
  logging.basicConfig(level=logging.INFO)
  #process('src/Symbooglix/Analysis/LoopInfo.cs')
  #return 0
  re_file = re.compile(r'^.+\.(cs|py)$')
  for dir_path, _, filenames in os.walk('./'):
    logging.info(f'Examing directory "{dir_path}"')
    for filename in filenames:
      if re_file.match(filename):
        full_path = os.path.abspath(os.path.join(dir_path, filename))
        logging.info(f'processing "{full_path}"')
        process(full_path)


if __name__ == '__main__':
  sys.exit(main())
