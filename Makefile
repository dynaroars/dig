
test_general_requirements:
	$(info >>> Testing General Requirements)
	sage helpers/check_requirements.py

test_doctests:
	$(info >>> Testing Python Doctests)
	PYTHONPATH=$PYTHONPATH:. sage -t helpers/miscs.py

install_miniconda_sympy_z3:
	$(info >>> Installing SymPy and Z3)


all: test_general_requirements test_doctests
	$(info >>> All Done)


# SUBDIRS := $(wildcard */.)

# all: $(SUBDIRS)
# $(SUBDIRS):
# 	$(MAKE) -C $@

# .PHONY: all $(SUBDIRS)

clean:
	rm -rf CIVLREP
	rm -rf *.pyo *.pyc *~
	rm -rf data/*.pyo data/*.pyc data/*~
	rm -rf data/invs/*.pyo data/invs/*.pyc data/invs/*~
	rm -rf data/poly/*.pyo data/poly/*.pyc data/poly/*~
	rm -rf cegir/*.pyo cegir/*.pyc cegir/*~
