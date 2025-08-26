#!/usr/bin/env python

import os
import re

configure_target = []
regdef_target = []
build_target = []
files_target = []

# walk through all sub-directories (root) and
# give me all directories (dirs) and (files)
# in each of these sub-directories ...

for root, dirs, files in os.walk(".", followlinks=False):
    m = re.search('^[\.\/\_\dA-Z]+$', root)
    if not m:
        continue

    for file in files:
        if file == "makefile.local":

            filename = os.path.join(root, file)

            with open(filename, 'r') as f:
                content = f.readlines()
                for line in content:

                    m = re.search('^configure:', line)
                    if m and root not in configure_target:
                        configure_target.append(root)

                    m = re.search('^regdef:', line)
                    if m and root not in regdef_target:
                        regdef_target.append(root)

                    m = re.search('^build:', line)
                    if m and root not in build_target:
                        build_target.append(root)

                    m = re.search('^files:', line)
                    if m and root not in files_target:
                        files_target.append(root)

# in-place sorting ...
configure_target.sort()
regdef_target.sort()
build_target.sort()
files_target.sort()

print("")
print(".PHONY: configure regdef build files")
print("")
print("configure::")
for root in configure_target:
    print("\t${{MAKE}} -B -C {0} -f makefile.local $@".format(root))

print("")
print("regdef:: configure")
for root in regdef_target:
    print("\t${{MAKE}} -B -C {0} -f makefile.local $@".format(root))
print("\t${MAKE} links")

print("")
print("build:: regdef")
for root in build_target:
    print("\t${{MAKE}} -B -C {0} -f makefile.local $@".format(root))
print("\t${MAKE} links")

print("")
print("files:: build")
for root in files_target:
    if root not in configure_target and root not in regdef_target and root not in build_target:
        print("\t${{MAKE}} -B -C {0} -f makefile.local $@".format(root))

print("")

