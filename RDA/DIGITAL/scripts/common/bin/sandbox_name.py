#!/usr/bin/env python

import sys
import re

parts = sys.argv[1].split('/')[::-1]
if "" in parts:
  parts.remove("")

for part in parts:
  if re.search("\d\d\d\d\d", part):
    print(part)
    exit()
  if re.search("\d\d\d\.\d\d", part):
    print(part)
    exit()
  if re.search("\d\d\d\_\d\d", part):
    print(part)
    exit()

print(parts[0])

