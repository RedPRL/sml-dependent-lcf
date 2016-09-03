#!/bin/bash

LIBS=$(pwd)/lib

mlton -mlb-path-var "LIBS $LIBS" dependent_lcf.mlb
mlton -mlb-path-var "LIBS $LIBS" nominal_lcf.mlb
