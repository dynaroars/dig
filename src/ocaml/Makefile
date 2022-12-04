OCAML_OPTIONS = \
  -I /usr/lib/ocaml/goblint-cil/ \
  -I /usr/lib/ocaml/zarith/ \
OCAMLC =        ocamlc                          $(OCAML_OPTIONS)
OCAMLOPT =      ocamlopt                        $(OCAML_OPTIONS)
OCAMLDEP =      ocamldep                        $(OCAML_OPTIONS)
OCAMLLEX =      ocamllex

all: instr.exe verify.exe

%.cmo: %.ml
	@if [ -f $*.mli -a ! -f $*.cmi ] ; then $(OCAMLC) -c -g $*.mli ; fi
	$(OCAMLC) -c -g $*.ml
	@$(OCAMLDEP) $*.ml > $*.d

%.cmx: %.ml
	@if [ -f $*.mli -a ! -f $*.cmi ] ; then $(OCAMLC) -c -g $*.mli ; fi
	$(OCAMLOPT) -c $*.ml
	@$(OCAMLDEP) $*.ml > $*.d

%.cmi: %.mli
	$(OCAMLC) -c -g $*.mli

%.ml: %.mll
	$(OCAMLLEX) $*.mll

INSTR_MODULES = \
	common.cmo \
	instr.cmo \

instr.exe: $(INSTR_MODULES:.cmo=.cmx)
		$(OCAMLOPT) -o $@ unix.cmxa str.cmxa zarith.cmxa goblintCil.cmxa $^

VERIFY_MODULES = \
	common.cmo \
	verify.cmo \

verify.exe: $(VERIFY_MODULES:.cmo=.cmx)
		$(OCAMLOPT) -o $@ unix.cmxa str.cmxa zarith.cmxa goblintCil.cmxa $^

clean:
	rm -f *.cmo *.cmi *.d *.cmx *.dx *.o instr.exe
	rm -rf *.pyc *.pyo
