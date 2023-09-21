from common0 import isnum

def check_all():
    """

    EXAMPLES:

    sage: check_all()
    Good to go!
    
    """
    check_sage()
    check_platform()
    check_z3()
    print 'Good to go!'


def check_sage(min_version=5.1):
    """
    Check if the requirement for Sage is met
    """
    v = version()
    v = v.replace(',','')
    v = v.split()
    v = [v_ for v_ in v if isnum(v_)]
    assert len(v)==1, 'Cannot obtain Sage version'
    v = float(v[0])
    
    assert v >= min_version, \
        "Sage needs at least version %g (found version %g)"%(min_version,v)


def check_platform(supported_platforms=['darwin','linux3']):
    """
    Check if the requirement for platform is met. 
    Either Mac OS or Linux is fine
    """
    p = sys.platform
    assert p.lower() in supported_platforms, "Unsupported platform '%s'"%p
               
def check_z3():
    """
    Check if Z3py API can be loaded properly
    """

    try:
        import z3
    except Exception:
        raise AssertionError('Cannot import z3py API. Check your SAGEPATH env')


