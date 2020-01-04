
test_general_requirements:
	$(info >>> Testing General Requirements)
	sage3 helpers/check_requirements.py

test_doctests:
	$(info >>> Testing Python Doctests)
	export SAGE_PATH=$Z3/src/api/python:.
	sage -t helpers/miscs.py

test: test_general_requirements test_doctests
	$(info >>> All Done)
clean:
	rm -rf *.pyo *.pyc *~
	rm -rf data/*.pyo data/*.pyc data/*~
	rm -rf data/invs/*.pyo data/invs/*.pyc data/invs/*~
	rm -rf data/poly/*.pyo data/poly/*.pyc data/poly/*~
	rm -rf cegir/*.pyo cegir/*.pyc cegir/*~
