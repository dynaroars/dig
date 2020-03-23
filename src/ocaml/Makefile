OCAML_OPTIONS = \
  -I /home/SHARED/Devel/CIL/cil/_build/src \
  -I /home/SHARED/Devel/CIL/cil/_build/src/ext \
  -I /home/SHARED/Devel/CIL/cil/_build/src/frontc \
  -I /home/SHARED/Devel/CIL/cil/_build/src/ocamlutil \

OCAMLC =        ocamlc                          $(OCAML_OPTIONS)
OCAMLOPT =      ocamlopt                        $(OCAML_OPTIONS)
OCAMLDEP =      ocamldep                        $(OCAML_OPTIONS)
OCAMLLEX =      ocamllex 

all: instr.exe

#coverage.exe preproc.exe instr.exe spy.exe modify.exe 

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
		$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa $^


# COVERAGE_MODULES = \
# 	common.cmo \
# 	coverage.cmo \

# coverage.exe: $(COVERAGE_MODULES:.cmo=.cmx)
# 		$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa $^


# INSTR_MODULES = \
# 	common.cmo \
# 	instr.cmo \

# instr.exe: $(INSTR_MODULES:.cmo=.cmx)
# 	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa $^


# SPY_MODULES = \
# 	common.cmo \
# 	modtemplate.cmo\
# 	spy.cmo \

# spy.exe: $(SPY_MODULES:.cmo=.cmx)
# 	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa $^


# MODIFY_MODULES = \
# 	common.cmo \
# 	modtemplate.cmo\
# 	modify.cmo \

# modify.exe: $(MODIFY_MODULES:.cmo=.cmx)
# 	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa $^

clean:
	rm -f *.cmo *.cmi *.d *.cmx *.dx *.o instr.exe 
	rm -rf *.pyc *.pyo
