#!/usr/bin/env python

import subprocess
import re
import sys
import os
import getopt

Event = {}
Location = {}
Node  = []
Edge = {}
po = {}
thread = []
num_inst = {} 
process = {}
indexL1 = {}
addr_map = {}
cacheability = {}
readers = {}
writers = {}
region = {}
address = {}
br_out = {}
br_pred = {}

variables = { "PA0" : "PA0",
              "PA1" : "PA1",
              "PA2" : "PA2",
              "PA3" : "PA3",
              "PA4" : "PA4",
              "PA5" : "PA5",
              "PA6" : "PA6",
              "PA7" : "PA7",
              "PA8" : "PA8",
              "PA9" : "PA9",
              "PA10" : "PA10"
            }

def printHeader(fout):
  # Print header
  fout.write("digraph G {\n")
  fout.write("\tlayout=neato;\n")
  fout.write("\toverlap=scale;\n")
  fout.write("\tsplines=true;\n")
  fout.write("\tlabel=\"Final\";\n")

def createEvents(fout):
  # Event labels
  # E.g., n3_0_label [label="Inst 3\nRead x 1\n";pos="5,0.5!";shape=none];

  inst_id = 0
  col_idx = 1
  for thd_id in range(len(thread)):
    first_inst = thread[thd_id]

    (Event[first_inst])[0] = inst_id
    (Event[first_inst])[1] = thd_id
    (Event[first_inst])[2] = col_idx

    fout.write("\tn" + str(inst_id) + "_0_label [label=\"")
    if first_inst in process:
      fout.write(process[first_inst] + ".I")
    else:
      fout.write("I")

    fout.write(str(inst_id)  + "\\n" + first_inst)

    if first_inst in br_pred:
      fout.write(" P" + br_pred[first_inst] + ", " + br_out[first_inst])
    else:
      if address[first_inst] in cacheability:
        fout.write("." + cacheability[address[first_inst]])

      fout.write(" " + address[first_inst])
      if address[first_inst] in addr_map:
        fout.write("(" + addr_map[address[first_inst]] + ":" + region[addr_map[address[first_inst]]] + ")")
      fout.write("\\n")
      if address[first_inst] in indexL1:
        fout.write(indexL1[address[first_inst]])
    fout.write("\\n\";pos=\"" + str(col_idx) + ",0.5!\";shape=none];\n")



    inst_id += 1
    col_idx += 1

    curr_inst = first_inst
    while curr_inst in po:
      num_inst[first_inst] += 1
      curr_inst = po[curr_inst]

      (Event[curr_inst])[0] = inst_id
      (Event[curr_inst])[1] = thd_id
      (Event[curr_inst])[2] = col_idx

      fout.write("\tn" + str(inst_id) + "_0_label [label=\"")
      if curr_inst in process:
        fout.write(process[curr_inst] + ".I")
      else:
        fout.write("I")

      fout.write(str(inst_id) + "\\n" + curr_inst)

      if curr_inst in br_pred:
        fout.write(" P" + br_pred[curr_inst] + ", " + br_out[curr_inst])
      else:
        if address[curr_inst] in cacheability:
          fout.write("." + cacheability[address[curr_inst]])
        fout.write(" " + address[curr_inst])
        if address[curr_inst] in addr_map:
          fout.write("(" + addr_map[address[curr_inst]] + ":" + region[addr_map[address[curr_inst]]] + ")")

      fout.write("\\n")
    
      if curr_inst in address:
        if address[curr_inst] in indexL1:
          fout.write(indexL1[address[curr_inst]])

      fout.write("\\n\";pos=\"" + str(col_idx) + ",0.5!\";shape=none];\n")
      


      inst_id += 1
      col_idx += 1

    col_idx += 1


def createLocations(fout):
  # Location labels
  # E.g., l0_0_label [label="Fetch";pos="0,-0!";shape=none]; 
  col_idx = 0
  for i in range(len(thread)):
    for loc in Location:
      fout.write("\tl" + str(col_idx) + "_" + str(Location[loc]) + "_label [label=\"" + loc + "\";pos=\"" + str(col_idx) + ",-" + str(Location[loc]) + "!\";shape=none];\n")
	
    col_idx += num_inst[thread[i]] + 1

def createNodes(fout):
  # Create nodes
  # E.g., n0_0_0_0_Write_x_1_at_0_2 [shape=circle;label="";pos="1,-2!";];
  for node in Node:
    node_array = node.split("->")
    event = node_array[0]
    loc = node_array[1]

    inst_id_str = str((Event[event])[0])
    thd_id_str = str((Event[event])[1])
    col_idx_str = str((Event[event])[2])

    fout.write("\tn" + inst_id_str + "_" + thd_id_str + "_0_0_" + event + "_at_" + thd_id_str + "_" + str(Location[loc]) + " [shape=circle;label=\"\";pos=\"" + col_idx_str + ",-" + str(Location[loc]) + "!\";];\n")

def createEdges(fout):
  # Create edges
  # E.g., n2_1_0_0_Read_x_2_at_1_1 -> n4_1_0_0_MMFENCE__at_1_1 [label="66:PPO";constraint=false;color="darkgreen";fontcolor="darkgreen";];
  colors = { "urf"       : "aquamarine3",
             "uco"       : "blue",
             "ucoh_inter"      : "gray",
             "ucoh_intra"      : "gray",
             "ufr"       : "crimson",
             "uflush"	 : "navy",
             "ustb"      : "deeppink2",
             "ustb_flush"      : "deeppink2",
             "uvicl"     : "darkorchid",
             "ucci"      : "darkorchid",
             "udep"      : "green",
             "uhb_inter" : "chartreuse2",
             "uhb_intra" : "goldenrod1",
             "uhb_proc"  : "darkorange",
             "default"   : "black",
             "uhb_spec"  : "pink",
             "usquash"  : "pink",
             "ufence"    : "orange",
           }
    
  edge_id = 0
  for edge_set in Edge:
    for edge in Edge[edge_set]:
      edge_array = edge.split("->")

      event0 = edge_array[0]
      loc0 = edge_array[1]
      inst_id0_str = str((Event[event0])[0])
      thd_id0_str = str((Event[event0])[1])

      event1 = edge_array[2]
      loc1 = edge_array[3]
      inst_id1_str = str((Event[event1])[0])
      thd_id1_str = str((Event[event1])[1])

      if edge_set in colors:
        color = colors[edge_set]
      else:
        color = colors["default"]

      fout.write("\tn" + inst_id0_str + "_" + thd_id0_str + "_0_0_" + event0 + "_at_" + thd_id0_str + "_" + str(Location[loc0]) + " -> n"  +inst_id1_str + "_" + thd_id1_str + "_0_0_" + event1 + "_at_" + thd_id1_str + "_" + str(Location[loc1]) + "[label=\"" + edge_set + "\";constraint=false;color=\"" + color + "\";fontcolor=\"" + color + "\";];\n")

      edge_id += 1

# Print footer
def printFooter(fout):
  fout.write("}\n")



def main(argv):
  global Event
  global Location
  global Node
  global Edge
  global po
  global thread
  global num_inst
  global process
  global indexL1
  global addr_map
  global cacheability
  global readers
  global writers
  global region
  global address
  global br_pred
  global br_out

  index = 0;

  infile = ""
  ofile_prefix = ""
  checkmate = ""
  graphdir = "."

  usage_string = "\nusage: \t release-generate-graphs.py [arguments] \
                 \n\nDescription: \tConvert Alloy output file into uhb graphs (.gv files). \
                 \n\nArguments: \
                 \n\t-h or --help \t\t\t\t Display this help and exit \
                 \n\t-i or --input <Alloy_outfile> \t\t File containing CheckMate-synthesized RMF output \
                 \n\t-c or --checkmate <checkmate_fn> \t\t Name of checkmate module imported for synthesis \
                 \n\t-o or --output <graph_prefix> \t\t Prefix for output graph files \
                 \n\t-g or --graphs <graph_dir> \t\t Directory for outputs graph files; default is current directory";

  try:
    opts, args = getopt.getopt(argv,"hi:c:o:g:",["help","input","checkmate","output","graphs"]);

  except getopt.GetoptError:
    print usage_string;
    sys.exit(1)

  for opt, arg in opts:
    if opt in ("-h", "--help"):
      print usage_string;
      sys.exit()

    elif opt in ("-i", "--input"):
      infile = arg

    elif opt in ("-c", "--checkmate"):
      checkmate = arg + "/"    

    elif opt in ("-o", "--output"):
      ofile_prefix = arg

    elif opt in ("-g", "--graphs"):
      graphdir = arg

  if not os.path.isfile(os.path.expanduser(infile)):
    print "ERROR: select a valid Alloy input file"
    print usage_string;
    sys.exit(1)

  if not os.path.isdir(os.path.expanduser(graphdir)):
    print "ERROR: invalid graph output directory"
    print usage_string;
    sys.exit(1)

  graphdir += "/graphs"
  if not (os.path.exists(graphdir) and os.path.isdir(graphdir)):
    os.makedirs(graphdir);

  print infile
  with open(infile, 'r') as fin:
    for line in fin:
      if checkmate in line:
        line = line.replace(checkmate, "")

      if "Event<:NodeRel=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Node = (m.group(1)).split(", ")
      
      if "Event<:urf=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["urf"] = (m.group(1)).split(", ")
      
      if "Event<:uco=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["uco"] = (m.group(1)).split(", ")
      
      if "Event<:ucoh_inter=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["ucoh_inter"] = (m.group(1)).split(", ")
      
      if "Event<:ucoh_intra=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["ucoh_intra"] = (m.group(1)).split(", ")
      
      if "Event<:uflush=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["uflush"] = (m.group(1)).split(", ")
      
      if "Event<:ufr=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["ufr"] = (m.group(1)).split(", ")
      
      if "Event<:udep=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["udep"] = (m.group(1)).split(", ")
      
      if "Event<:usquash=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["usquash"] = (m.group(1)).split(", ")
      
      if "Event<:ustb=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["ustb"] = (m.group(1)).split(", ")
      
      if "Event<:ustb_flush=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["ustb_flush"] = (m.group(1)).split(", ")
      
      if "Event<:uvicl=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["uvicl"] = (m.group(1)).split(", ")
      
      if "Event<:ucci=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["ucci"] = (m.group(1)).split(", ")
      
      if "Event<:uhb_inter=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["uhb_inter"] = (m.group(1)).split(", ")
      
      if "Event<:uhb_intra=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["uhb_intra"] = (m.group(1)).split(", ")
      
      if "Event<:uhb_proc=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["uhb_proc"] = (m.group(1)).split(", ")
   
      if "Event<:uhb_spec=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["uhb_spec"] = (m.group(1)).split(", ")
   
      if "Event<:ufence=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        if m:
          Edge["ufence"] = (m.group(1)).split(", ")
   
      if "Event<:po=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        po_array = (m.group(1)).split(", ")
        for po_rel in po_array:
          po_rel_array = po_rel.split("->")
          po[po_rel_array[0]] = po_rel_array[1]
  
      if "Event=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        event_array = (m.group(1)).split(", ")
        thread = event_array
  
        for event in event_array:
          Event[event] = [-1, -1, -1]
         
      if "Location=" in line:
        line = line.replace("$", "")
        m = re.search('={(.+?)}', line)
        loc_array = (m.group(1)).split(", ")
        for i in range(len(loc_array)):
          Location[loc_array[i]] = i

      if "Event<:process=" in line:
        line = line.replace("$", "")
        line = line.replace("Victim0", "Victim")
        line = line.replace("Attacker0", "Attacker")
        m = re.search('={(.+?)}', line)
        proc_array = (m.group(1)).split(", ")
        for proc_rel in proc_array:
          proc_rel_array = proc_rel.split("->")
          process[proc_rel_array[0]] = proc_rel_array[1]

      if "Branch<:outcome=" in line:
        line = line.replace("$", "")
        line = line.replace("Not", "N")
        line = line.replace("Taken0", "T")
        m = re.search('={(.+?)}', line)
        if not m:
          continue
        br_out_array = (m.group(1)).split(", ")
        for br_out_rel in br_out_array:
          br_out_rel_array = br_out_rel.split("->") 
          br_out[br_out_rel_array[0]] = br_out_rel_array[1]

      if "Branch<:prediction=" in line:	
        line = line.replace("$", "")
        line = line.replace("Not", "N")
        line = line.replace("Taken0", "T")
        m = re.search('={(.+?)}', line)
        if not m:
          continue
        br_pred_array = (m.group(1)).split(", ")
        for br_pred_rel in br_pred_array:
          br_pred_rel_array = br_pred_rel.split("->") 
          br_pred[br_pred_rel_array[0]] = br_pred_rel_array[1]

      if "MemoryEvent<:address=" in line or "CacheFlush<:flush_addr" in line:
        line = line.replace("$", "")
        line = line.replace("VirtualAddress", "VA")
        m = re.search('={(.+?)}', line)
        if not m:
          continue
        addr_array = (m.group(1)).split(", ")
        for addr_rel in addr_array:
          addr_rel_array = addr_rel.split("->")
          address[addr_rel_array[0]] = addr_rel_array[1]

      if "VirtualAddress<:indexL1=" in line:
        line = line.replace("$", "")
        line = line.replace("VirtualAddress", "VA")
        line = line.replace("CacheIndexL1", "L1")
        m = re.search('={(.+?)}', line)
        index_array = (m.group(1)).split(", ")
        for index_rel in index_array:
          index_rel_array = index_rel.split("->")
          indexL1[index_rel_array[0]] = index_rel_array[1]

      if "VirtualAddress<:map=" in line:
        line = line.replace("$", "")
        line = line.replace("VirtualAddress", "VA")
        line = line.replace("PhysicalAddress", "PA")
        m = re.search('={(.+?)}', line)
        map_array = (m.group(1)).split(", ")
        for map_rel in map_array:
          map_rel_array = map_rel.split("->")
          if map_rel_array[1] in variables:
            addr_map[map_rel_array[0]] = variables[map_rel_array[1]]
          else:
            addr_map[map_rel_array[0]] = map_rel_array[1]

      if "VirtualAddress<:cacheability=" in line:
        line = line.replace("$", "")
        line = line.replace("VirtualAddress", "VA")
        line = line.replace("NonCacheable0", "NC")
        line = line.replace("Cacheable0", "C")
        m = re.search('={(.+?)}', line)
        cache_array = (m.group(1)).split(", ")
        for cache_rel in cache_array:
          cache_rel_array = cache_rel.split("->")
          cacheability[cache_rel_array[0]] = cache_rel_array[1]

      if "PhysicalAddress<:readers=" in line:
        line = line.replace("$", "")
        line = line.replace("PhysicalAddress", "PA")
        line = line.replace("Victim0", "Victim")
        line = line.replace("Attacker0", "Attacker")
        m = re.search('={(.+?)}', line)
        if not m:
          continue
        readers_array = (m.group(1)).split(", ")
        for readers_rel in readers_array:
          readers_rel_array = readers_rel.split("->")
          if readers_rel_array[0] in variables:
            readers[variables[readers_rel_array[0]]] = readers_rel_array[1]
          else:
            readers[readers_rel_array[0]] = readers_rel_array[1]

      if "PhysicalAddress<:writers=" in line:
        line = line.replace("$", "")
        line = line.replace("PhysicalAddress", "PA")
        line = line.replace("Victim0", "Victim")
        line = line.replace("Attacker0", "Attacker")
        m = re.search('={(.+?)}', line)
        if not m:
          continue
        writers_array = (m.group(1)).split(", ")
        for writers_rel in writers_array:
          writers_rel_array = writers_rel.split("->")
          if writers_rel_array[0] in variables:
            writers[variables[writers_rel_array[0]]] = writers_rel_array[1]
          else:
            writers[writers_rel_array[0]] = writers_rel_array[1]

      if "PhysicalAddress<:region=" in line:
        line = line.replace("$", "")
        line = line.replace("PhysicalAddress", "PA")
        line = line.replace("Victim0", "Victim")
        line = line.replace("Attacker0", "Attacker")
        m = re.search('={(.+?)}', line)
        if not m:
          continue
        region_array = (m.group(1)).split(", ")
        for region_rel in region_array:
          region_rel_array = region_rel.split("->")
          if region_rel_array[0] in variables:
            region[variables[region_rel_array[0]]] = region_rel_array[1]
          else:
            region[region_rel_array[0]] = region_rel_array[1]

      if "END INSTANCE" in line:
        removal = []
        for event in thread:
          if event in po:
            removal.append(po[event])

        for event in removal:
          thread.remove(event)

        for event in thread:
          num_inst[event] = 1

        fout = open(graphdir + "/" + ofile_prefix + '-' + str(index) + '.gv', 'w')

        printHeader(fout)
        createEvents(fout)
        createLocations(fout)
        createNodes(fout)
        createEdges(fout)
        printFooter(fout)

        fout.close()
        
        Event = {}
        Location = {}
        Node = []
        Edge = {}
        po = {}
        thread = []
        num_inst = {} 
        process = {}
        indexL1 = {}
        addr_map = {}
        cacheability = {}
        address = {}
        br_out = {}
        br_pred = {}
  
        index += 1
  fin.close()

  return

if __name__ == "__main__":
   main(sys.argv[1:])
