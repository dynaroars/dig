echo "For these to work properly, set your SAGE_PATH to this directory!"

#Test all the unit tests from files for Invariant Generators
sage -t check_requirements.py
sage -t common.py
sage -t miscs.py
sage -t iexp.py
sage -t smt_z3py.py
sage -t refine.py
sage -t inv_polynomials.py
sage -t inv_arrays.py
sage -t invgen.py
sage -t benchmark.py


#sage -t iconstructs.py
