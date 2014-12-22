#!/usr/bin/env python
# vim: set sw=2 ts=2 softtabstop=2:
"""
Check Termination Counter YAML
Simple utility to read YAML file and check
the value of a key is as expected.
"""
import argparse
import logging
import pprint
import sys
import yaml


def main(args):
  logging.basicConfig(level=logging.DEBUG)
  parser = argparse.ArgumentParser(description=__doc__)
  parser.add_argument('yaml_file', type=argparse.FileType('r'), help='YAML file to open')
  parser.add_argument('key', help='Top level key to read')
  parser.add_argument('expected_value',
                      help='The expected string representation of the' +
                           ' value associated with the specified key'
                     )

  pargs = parser.parse_args(args)

  try:
    data = yaml.load(pargs.yaml_file)
  except Exception as e:
    logging.error('Failed to load YAML file:\n{type}\n{msg}'.format(type=str(type(e)), msg=e))
    return 1

  logging.info("Loaded data :\n{}".format(pprint.pformat(data)))

  assert len(pargs.key) > 0
  assert len(pargs.expected_value) > 0
  assert data != None

  if not pargs.key in data:
    logging.error('{key} is not a top level key in the YAML file'.format(key=pargs.key))
    return 2

  if str(data[pargs.key]) != pargs.expected_value:
    logging.error('Value mismatch, expected "{expected}" != "{actual}"'.format(expected=pargs.expected_value, actual=data[pargs.key]))
    return 3

  logging.info('values match')
  return 0

if __name__ == '__main__':
  sys.exit(main(sys.argv[1:]))
