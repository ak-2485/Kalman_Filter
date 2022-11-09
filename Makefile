COQC=coqc
COQDEP=coqdep
VCFLOAT_LOC=../vcfloat/vcfloat
COQFLAGS= -Q $(VCFLOAT_LOC) vcfloat

all: Mean.vo  _CoqProject mean_error.vo 

_CoqProject: Makefile
	echo $(COQFLAGS) >_CoqProject

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v

depend: 
	$(COQDEP) $(COQFLAGS) *.v > .depend


include .depend

clean : 
	rm -rf weight weight.v *.o *.glob *.vo *.vok *.vos .*.aux

