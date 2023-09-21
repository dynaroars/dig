def check_all():
    """
    sage: check_all()
    Checking minimum requirements
    ...
    Platform .. OK
    ...
    SAGE .. OK
    ...
    Z3 .. OK
    ...
    External programs .. OK
    Have fun with DIG !

    """
    print('Checking minimum requirements')
    check_platform()    
    check_sage()
    check_z3()
    check_ext_progs()
    print 'Have fun with DIG !'


def check_platform():
    """
    Check if the requirement for platform is met. 
    """
    p = sys.platform.lower()
    print("* System: '{}'".format(p))
    assert p.startswith('linux'), "Unsupported platform '{}'".format(p)
    print "Platform .. OK"
               
def check_sage(min_version="6.2"):
    """
    Check if the requirement for Sage is met
    """
    try:
        from distutils.version import StrictVersion
        from sage.env import SAGE_VERSION, SAGE_DATE, SAGE_SRC

        print('* SAGE: {}, release date: {}, in "{}"'
              .format(SAGE_VERSION, SAGE_DATE, SAGE_SRC))
        assert StrictVersion(SAGE_VERSION) >= StrictVersion(min_version), \
            ("Need SAGE version >= {} (you have {})"
             .format(min_version, SAGE_VERSION))
        print("SAGE .. OK")

    except Exception as e:
        raise

def check_z3():
    """
    Check if Z3 API can be loaded properly
    """
    try:
        import z3
        print '* Z3 version: {}'.format(z3.get_version_string())
        print("Z3 .. OK")
        
    except Exception as e:
        from sage.env import SAGE_SRC
        msg = (("Try Adding z3py API to SAGE_PATH\n" 
               "E.g. in ~/.bash_profile\n"
               "export SAGE={}\n"
               "export PATH=$SAGE:$PATH\n"
               "export SAGE_PATH=$DROPBOX/git/common_python:$DIG:$Z3/src/api/python")
               .format(SAGE_SRC))

        raise AssertionError('Cannot import Z3 API.\n{}'.format(msg))

def check_ext_progs():
    """
    Check if external programs exist
    """
    try:
        mpp_prog = "compute_ext_rays_polar"
        import subprocess
        subprocess.call([mpp_prog])
        print("* compute_ext_rays_polar")
        
        print("External programs .. OK")
    except OSError as e:
        if e.errno == os.errno.ENOENT:
            msg = (("'{}' not found (install 'tpplib'), "
                    "will not infer min/max-plus invariants")
                   .format(mpp_prog))
            print(msg) 
        else:
            # Something else went wrong while trying to run `cmd`
            raise
                        
if __name__ == "__main__":

    print('Runs this script in Sage\n'
          'E.g.,\n'
          'sage: %attach dig_check_requirements.py\n'
          'sage: check_all()\n')
    


