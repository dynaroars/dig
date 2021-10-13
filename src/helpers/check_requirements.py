def check_all():
    print('Checking minimum requirements')
    check_platform()
    check_sympy()
    check_z3()
    # check_ext_progs()
    print('Everything seems OK.  Have fun with DIG !')


def check_platform():
    """
    Check if the requirement for platform is met.
    """
    import sys
    p = sys.platform.lower()
    print("* System: '{}'".format(p))
    assert p.startswith('linux'), "platform '{}' is not supported".format(p)
    print("Platform .. OK")


def check_sympy():
    """
    Check if the requirement for Sage is met
    """
    try:
        import sympy
        print(f"* Sympy: {sympy.__version__}")
    except Exception as e:
        raise


def check_z3():
    """
    Check if Z3 API can be loaded properly
    """
    try:
        import z3
        print('* Z3 version: {}'.format(z3.get_version_string()))

    except Exception as e:
        from sage.env import SAGE_SRC
        msg = (("Try Adding z3py API to PYTHONPATH\n"
                "E.g. in ~/.bash_profile\n"
               "export PYTHONPATH=$Z3/src/api/python:$PYTHONPATH")
               .format(SAGE_SRC))

        raise AssertionError('Cannot import Z3 API.\n{}'.format(msg))


def check_ext_progs():
    """
    Check if external programs exist
    """

    import subprocess

    def run(prog, args=[]):
        cmd = [prog] + args
        subprocess.call(cmd)
        print("* {}".format(prog))

    # check JPF
    try:
        import os
        from path import Path
        prog = Path(os.path.expandvars("$JPF_HOME"))
        prog = prog / "jpf-core/bin/jpf"
        run(prog)
    except OSError as e:
        import errno
        if e.errno == errno.ENOENT:
            msg = ((f"'{prog}' not found (install 'jpf'), "
                    "will not work with JAVA programs"))
            print(msg)
        else:
            # Something else went wrong while trying to run `cmd`
            raise

    # Check CIVL
    try:
        import os
        from path import Path
        prog = Path(os.path.expandvars("$CIVL_HOME"))
        prog = prog / "lib" / "civl-1.20_5259.jar"
        run(prog)
    except OSError as e:
        import errno
        if e.errno == errno.ENOENT:
            msg = ((f"'{prog}' not found (install 'civl'), "
                    "will not work with C programs"))
            print(msg)
        else:
            if e.errno == errno.EACCES:
                pass  # expected
            else:  # Something else went wrong while trying to run `cmd`
                raise

    print("External programs .. OK")


if __name__ == "__main__":
    check_all()
