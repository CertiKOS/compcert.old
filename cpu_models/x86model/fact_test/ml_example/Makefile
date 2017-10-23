#
# Pure OCaml, no packages, no _tags
#

# bin-annot is required for Merlin and other IDE-like tools

.PHONY:	all clean byte native elf

COQINCLUDES = -R ../../Model X86Model -R ../../../shared Shared
COQC = coqc $(COQINCLUDES)

OCB_FLAGS = -use-ocamlfind -tag bin_annot
OCB = 		ocamlbuild -lib nums $(OCB_FLAGS) 
ENCODE = Encode

all: native byte lib elf

clean:
	$(OCB) -clean

lib: 
	$(OCB) $(ENCODE).cma
	$(OCB) Elf.cma

native:
	$(OCB) $(ENCODE).native
	$(OCB) fac.native

byte:
	$(OCB) $(ENCODE).byte
	$(OCB) fac.native

extract:
	$(COQC) extract.v
