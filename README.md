# Dynamic-Code-Reordering-with-Pintool
00460275 Binary Translation and Optimization- Technion
Overview
This project implements a Pin-based dynamic binary instrumentation tool that profiles and optimizes program execution through Code Reordering of basic blocks. The tool spawns a parallel thread that reorders frequently executed basic blocks and executes them from a separate translation cache (TC2) to improve performance.

------------ INSTRUCTIONS TO USE THE TOOL:-----------------

creating an .so file and running with pin tool instructions


1. the first step is to create our directory:
	 go to the directory of the pintool (this path will be called from now on <pindir>)
	 $ cd source/tools
       	 create a new directory for the exercise: $ mkdir project
	 copy the .cpp, makefile and makefile.rules into the new directory

2.create the .so file: $ make <filename>.test  (filename is the name of the cpp file, in this case the command is $ make project.test)
	this will create a directory called obj-intel64 and the .so file will be inside

3.to run your executable with the instrumentation (from the directory you created before i.e project):
	 <pindir>/pin –t project.so -create_tc2 -prof_time <x>  -- ./bzip2 –k –f input-long.txt 
