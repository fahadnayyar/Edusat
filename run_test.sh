#!/bin/bash

FILES1=./test/unsat/*.cnf
FILES2=./test/sat/*.cnf

for f in $FILES1
do
  echo "Processing $f test-case file..."
  ./edusat $f
  ./edusat $f
done

for f in $FILES2
do
  echo "Processing $f test-case file..."
  ./edusat $f
  ./edusat $f
done