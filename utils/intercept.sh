#!/bin/bash

cat | tee X.log | z3 $@
