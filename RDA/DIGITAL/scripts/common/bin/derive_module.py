#!/common/run/synopsys/vcs/O-2018.09/bin/Python-2.7.15/bin/python

if __name__ == "__main__":

  import os
  import sys
  import shutil
  import argparse

  def check_dir(dir):
    if not os.path.exists(dir):
      print("ERROR: Directory {0} does not exists !".format(dir))
      exit()
    if not os.path.isdir(dir):
      print("ERROR: {0} exists, but is not a directory !".format(dir))
      exit()

  def mkdir(dir):
    if not os.path.exists(dir):
      os.makedirs(dir)
    else:
      check_dir(dir)

  def copy_recursive_overwrite(src, dst):
    if os.path.isdir(src):
      mkdir(dst)
      for f in os.listdir(src):
        copy_recursive_overwrite(os.path.join(src, f), os.path.join(dst, f))
    else:
      shutil.copyfile(src, dst)


  ap = argparse.ArgumentParser()
  ap.add_argument("-b", "--base", type=str, required=True, help="base directory (e.g. ./STD_COMPONENTS/AHBL_SWITCH_LIB)")
  ap.add_argument("-d", "--derived", type=str, required=True, help="where to create derived directory (e.g. ./)")
  args = ap.parse_args()

  base_parts = args.base.split('/')[::-1]
  if '' in base_parts:
    base_parts.remove('')

  if base_parts[0] == "derive":
    source_dir = args.base
    base_name = base_parts[1]
  else:
    source_dir = os.path.join(args.base, "derive")
    base_name = base_parts[0]

  derived_parts = args.derived.split('/')[::-1]
  if '' in derived_parts:
    derived_parts.remove('')

  if derived_parts[0] == base_name:
    target_dir = args.derived
  else:
    target_dir = os.path.join(args.derived, base_name)

  check_dir(source_dir)
  copy_recursive_overwrite(source_dir, target_dir)


