#!/usr/bin/env python

import subprocess
import re
import sys
import os
import getopt

def main(argv):
  indir = ""
  outdir = ""

  usage_string = "\nusage: \t release-generate-images.py [arguments] \
                 \n\nDescription: \tConvert uhb graph files (.gv files) to .png files. \
                 \n\nArguments: \
                 \n\t-h or --help \t\t\t\t Display this help and exit \
                 \n\t-i or --input <graphs_dir> \t\t Path to directory containing input uhb graph files\
                 \n\t-o or --output <imgs_dir> \t\t Path to directory for output .png files" ;

  try:
    opts, args = getopt.getopt(argv,"hi:o:",["help","input","output"]);

  except getopt.GetoptError:
    print usage_string;
    sys.exit(1)

  for opt, arg in opts:
    if opt in ("-h", "--help"):
      print usage_string;
      sys.exit()

    elif opt in ("-i", "--input"):
      indir = arg

    elif opt in ("-o", "--output"):
      outdir = arg

  if not os.path.isdir(os.path.expanduser(indir)):
    print "ERROR: select a valid input directory"
    print usage_string;
    sys.exit(1)
 
  if not os.path.isdir(os.path.expanduser(outdir)):
    print "ERROR: select a valid output directory"
    print usage_string;
    sys.exit(1)

  found_error = False
  for file in os.listdir(indir):
    if file.endswith(".gv"):
      try: 
        cmd = "dot -Tpng " + indir + "/" + file + " -o " + outdir + "/" + file.replace("gv", "png")
        p = subprocess.Popen(cmd, shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, close_fds=True)
        output, error = p.communicate()

        if error:
          if not found_error:
            print "ERROR: the following file(s) are uable to be converted into a png:"
            found_error = True

      except OSError as e:
        print "OSError > ",e.errno
        print "OSError > ",e.strerror
        print "OSError > ",e.filename

      print file

  if found_error:
    print "\nThe most likely cause is that a checkmate import file was not specified when release-generate-graphs.py was run."
    print "Try re-running release-generate-graphs.py, this time speciying the checkmate import file."
    print usage_string;
    sys.exit(1)
  
  return

if __name__ == "__main__":
   main(sys.argv[1:])
