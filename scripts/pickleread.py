#!/usr/bin/env python3

import pickle
import sys

with open(sys.argv[1], "rb") as f:
    model = pickle.load(f)
    model.print()
