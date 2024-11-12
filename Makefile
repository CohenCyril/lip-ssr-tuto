# -*- Makefile -*-

# setting variables
COQPROJECT?=_CoqProject
COQMAKEOPTIONS=--no-print-directory

# Main Makefile
include Makefile.common

theories/%.v: lessons/%.mv
	tools/codeblocks.sh $< > $@
