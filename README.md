# checkmate

CheckMate is an approach and automated tool for determining if a microarchitecture is susceptible to formally specified classes of security exploits, and for synthesizing proof-of-concept exploit code when it is.

CheckMate is rooted in "microarchitectural happens-before" (μhb) graph analysis techniques used by piror memory consistency model verification tools: PipeCheck, CCICheck, COATCheck, and TriCheck.  Much of the terminology and naming comes from those tools. See those papers/websites for detail:

http://github.com/daniellustig/pipecheck

http://github.com/ymanerka/ccicheck

http://github.com/daniellustig/coatcheck

https://github.com/ctrippel/TriCheck

Also, find a link to a tutorial on these prior tools and their syntax here:

http://check.cs.princeton.edu


### Citing CheckMate

If you use our tool in your work, we would appreciate it if you cite our paper(s):

Caroline Trippel, Daniel Lustig, and Margaret Martonosi. 
  "CheckMate: Automated Exploit Program Generation for Hardware Security Verification", 
  *51st International Symposium on Microarchitecture (MICRO)*, Fukuoka, Japan, Octiober 2018.

Caroline Trippel, Yatin Manerkar, Daniel Lustig, Michael Pellauer, and Margaret Martonosi. 
  "TriCheck: Memory Model Verification at the Trisection of Software, Hardware, and ISA", 
  *22nd International Conference on Architectural Support for Programming Languages and
  Operating Systems (ASPLOS)*, Xi'an, China, April 2017.

Daniel Lustig+, Geet Sethi+, Margaret Martonosi, and Abhishek Bhattacharjee.
  "COATCheck: Verifying Memory Ordering at the Hardware-OS Interface",
  *21st International Conference on Architectural Support for Programming
  Languages and Operating Systems (ASPLOS)*, Atlanta, GA, April 2016.
  (+: joint first authors)

Yatin Manerkar, Daniel Lustig, Michael Pellauer, and Margaret Martonsi.
  "CCICheck: Using uhb Graphs to Verify the Coherence-Consistency Interface",
  *48th International Symposium on Microarchitecture (MICRO)*,
  Honolulu, HI, December 2015.

Daniel Lustig, Michael Pellauer, and Margaret Martonosi.  "PipeCheck:
  Specifying and Verifying Microarchitectural Enforcement of Memory Consistency
  Models", *47th International Symposium on Microarchitecture (MICRO)*,
  Cambridge UK, December 2014.

### Contacting the authors

If you have any comments, questions, or feedback, please contact Caroline Trippel at ctrippel@princeton.edu, or visit our GitHub page, github.com/ctrippel/checkmate.

### Status

At this point, CheckMate is a research tool rather than an industry-strength verification toolchain. We do appreciate any suggestions or feedback either in approach or in implementation.  If you are interested in any particular feature, missing item, or implementation detail, please contact the authors and we will try to help out as best we can.

## Building and Using CheckMate

### Prerequisites

CheckMate is currently written as an embedding of the μspec DSL (DSL used by the priror Check tools) in the Alloy DSL. Alloy runs as a Java appication. We use the latest build (at the time of publication), Alloy 4.2., which can be found here:

http://alloytools.org/download.html

Alloy 4.2 requires Java 6.

The remainder of CheckMate requires Python and has been tested with Python v2.7.5.