#!/usr/bin/env python

import subprocess
import re
import sys
import os
import getopt

def main(argv):
  filter_files = {}
  indir = ""

  usage_string = "\nusage: \t release-symmetry-reduction.py [arguments] \
                 \n\nDescription: \tRemove duplicate and isomorphic uhb graph files (.gv files). \
                 \n\nArguments: \
                 \n\t-h or --help \t\t\t\t Display this help and exit \
                 \n\t-i or --input <graphs_dir> \t\t Path to directory contianing uhb graph files to filter" ;

  try:
    opts, args = getopt.getopt(argv,"hi:",["help","input"]);

  except getopt.GetoptError:
    print usage_string;
    sys.exit(1)

  for opt, arg in opts:
    if opt in ("-h", "--help"):
      print usage_string;
      sys.exit()

    elif opt in ("-i", "--input"):
      indir = arg + "/"

  if not os.path.isdir(os.path.expanduser(indir)):
    print "ERROR: select a valid input directory"
    print usage_string;
    sys.exit(1)
 
  for fn in os.listdir(indir):
    if fn.endswith(".gv"):
      body = ""
      va_id = 0
      pa_id = 0
      l1_id = 0
      op_id = 0
      va_map = {}
      pa_map = {}
      l1_map = {}
      op_map = {}

      with open(indir + fn, 'r') as fin:
        for line in fin:
          br_pattern = re.search("n.*0_label\s\[label=(.*)(Branch([0-9]))(.*)", line)
          mem_pattern = re.search("n.*0_label\s\[label=\"(.*)(\\\)n(.*)\s(.*)\((.*):(.*)\).*(\\\)n(.*)(\\\)n\";.*", line)
          if mem_pattern:
            inst = mem_pattern.group(1)
            op = mem_pattern.group(3)
            va = mem_pattern.group(4)
            pa = mem_pattern.group(5)
            proc = mem_pattern.group(6)
            l1 = mem_pattern.group(8)

            op_pattern = re.search("(.*)([0-9])(.*)", op)
            if op_pattern:
              microop = op_pattern.group(1)
              microop_id = op_pattern.group(2)
              cacheability = op_pattern.group(3)

            if not va in va_map:
              va_map[va] = "VAn" + str(va_id)
              va_id += 1

            if not pa in pa_map:
              pa_map[pa] = "PAn" + str(pa_id)
              pa_id += 1           

            if not l1 in l1_map:
              l1_map[l1] = "L1n" + str(l1_id)
              l1_id += 1

            if not op in op_map:
              op_map[microop + str(microop_id)] = microop + "n" + str(op_id)
              op_id += 1

          elif br_pattern:
            op = br_pattern.group(2)

            if not op in op_map:
              op_map[op] = "Branchn" + str(op_id)
              op_id += 1

          cache_pattern = re.search("ucci", line)
          if cache_pattern:
            line = ""

          body += line

      for va in va_map:
        body = body.replace(va, va_map[va])
      for pa in pa_map:
        body = body.replace(pa, pa_map[pa])
      for l1 in l1_map:
        body = body.replace(l1, l1_map[l1])
      for op in op_map:
        body = body.replace(op, op_map[op])

      body_array = body.split("\n")

      match = 0
      for b in filter_files:
        if set(body_array) == set(b.split("\n")):
          filter_files[b].append(fn)
          match = 1
          break;

      if match == 0:
        filter_files[body] = []

      fin.close()
  
  for b in filter_files:
    for f in filter_files[b]:
      name = indir + f
      os.remove(name)
  
  return


if __name__ == "__main__":
   main(sys.argv[1:])
