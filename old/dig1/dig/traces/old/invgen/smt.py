### DO NOT USE -- DEPRECATED ###

import common as CM
from miscs import Miscs
from sage.all import *

class SMT(object):
    @staticmethod
    def bin_f(f,b,l):
        """
        sage: from smt import SMT
        sage: SMT.bin_f('(%s %s %s)','+',[1,2,3,4])
        '(+ (+ (+ 1 2) 3) 4)'
        """
        return reduce(lambda x,y:f%(b,x,y),l)

    @staticmethod
    def rop2str(op):
        d = {operator.ge:'>=',
             operator.gt:'>',
             operator.le:'<=',
             operator.lt:'<',
             operator.eq:'=',
             operator.ne:'!=',
             operator.add:'+',
             operator.sub:'-',
             operator.mul:'*',
             operator.div:'/',
             operator.pow:'^'}
             
        return d[op]

    
    @staticmethod
    def i2p(p,doReal=False):
        """
        infix to posfix format
        
        sage: var('x,y,z')
        (x, y, z)
        
        sage: from smt import SMT
        
        sage: SMT.i2p(3*x^-2 >= 8)
        '(>= (* (/ 1 (* x x)) 3) 8)'

        sage: SMT.i2p(y + x + 3/7*z)
        '(+ (+ x y) (* z (/ 3 7)))'

        sage: SMT.i2p(3*x -7/8*x^2)
        '(+ (* (* x x) (/ (- 7) 8)) (* x 3))'

        sage: SMT.i2p(3*x -7/8*x^2 - 9)
        '(+ (+ (* (* x x) (/ (- 7) 8)) (* x 3)) (- 9))'

        sage: SMT.i2p(-3*x - 4/7*x*3*y^2*z)
        '(+ (* (* (* x (* y y)) z) (/ (- 12) 7)) (* x (- 3)))'

        sage: SMT.i2p((x+y)^2)
        '(* (+ x y) (+ x y))'

        sag: SMT.i2p((x+1)^-1 + 5*z-7)
        '(+ (+ (* z 5) (/ 1 (+ x 1))) (- 7))'

        sage: SMT.i2p(((x+3)-1+y)^-2 + 5*z-1)
        '(+ (+ (* z 5) (/ 1 (* (+ (+ x y) 2) (+ (+ x y) 2)))) (- 1))'

        sage: SMT.i2p(((x+3)/y-1+z)^-2 + 5*(z^2/x^-1) -1)
        '(+ (+ (* (* x (* z z)) 5) (/ 1 (* (+ (+ z (* (+ x 3) (/ 1 y))) (- 1)) (+ (+ z (* (+ x 3) (/ 1 y))) (- 1))))) (- 1))'


        sage: SMT.i2p(((x+3)/y-1+z)^-2 + 5/7*(z^2/x^-1) - (1/8*y)^2)
        '(+ (+ (* (* x (* z z)) (/ 5 7)) 
        (/ 1 (* (+ (+ z (* (+ x 3) (/ 1 y))) (- 1)) 
        (+ (+ z (* (+ x 3) (/ 1 y))) (- 1))))) (* (* y y) (/ (- 1) 64)))'

        sage: SMT.i2p(((x+3)/y-1+z)^-2 + 5/7*(z^2/x^-1) - (1/8*y+1)^-2)
        '(+ (+ (* (* x (* z z)) (/ 5 7)) 
        (* (/ 1 (* (+ y 8) (+ y 8))) (- 64))) 
        (/ 1 (* (+ (+ z (* (+ x 3) (/ 1 y))) (- 1))
        (+ (+ z (* (+ x 3) (/ 1 y))) (- 1)))))'

        sage: SMT.i2p((2/3*y-1)^-2)
        '(* (/ 1 (* (+ (* y 2) (- 3)) (+ (* y 2) (- 3)))) 9)'


        sage: SMT.i2p((2.4/3.8*y-1.7)^-2.0)
        '(/ 1 (* (+ (* y 0.631578947368421) (- 1.70000000000000)) (+ (* y 0.631578947368421) (- 1.70000000000000))))'

        sage: SMT.i2p((2.0/3.2*y-1.7)^-1)  #note: 2.0/3.2 will be eval to 0.625 before passing to the fun
        '(/ 1 (+ (* y 0.625000000000000) (- 1.70000000000000)))'

        sage: SMT.i2p((2.0/3.2*y-1.7)^-1,doReal=True)
        '(/ 1.00000000000000 (+ (* y 0.625000000000000) (- 1.70000000000000)))'

        sage: SMT.i2p(((x+3)-1+y)^-2 + 5*z-1,doReal=True)
        '(+ (+ (* z 5.00000000000000) (/ 1.00000000000000 (* (+ (+ x y) 2.00000000000000) (+ (+ x y) 2.00000000000000)))) (- 1.00000000000000))'

        sage: SMT.i2p(1/3)
        '(/ 1 3)'

        sage: SMT.i2p(1/3,doReal=True)
        '(/ 1.00000000000000 3.00000000000000)'

        sage: SMT.i2p(x+1/3,doReal=True)
        '(+ x (/ 1.00000000000000 3.00000000000000))'

        sage: SMT.i2p((x+2)^2,doReal=True)
        '(* (+ x 2.00000000000000) (+ x 2.00000000000000))'
        """

        def toreal(v,doReal):
            v_ = v.n() if doReal else v
            if v_ < 0:
                v_ = '(- %s)'%abs(v_)
            else:
                v_ = '%s'%v_
            return v_

        def retval(p,doReal):
            if '/' in str(p):  #e.g., 5/7
                p = QQ(p)
                denom, numer = p.denominator(), p.numerator()
                return '(/ %s %s)'%(toreal(numer,doReal),toreal(denom,doReal))
            else:
                try:
                    return str(toreal(p,doReal))
                except Exception:
                    return p

        
        try:
            oprs = p.operands()
        except Exception:
            return retval(p,doReal)

        if CM.is_none_or_empty(oprs):
            return retval(p,doReal)


        else:
            doInverse = False
            op = p.operator()

            if op == operator.pow:
                _n,_p = oprs[0], Integer(oprs[1]) #x^-3 => [x,-3]
                doInverse = _p < 0 #x^-2 =>  1/(x^2)
                oprs = [_n] * abs(_p)
                op = operator.mul

            oprs = [SMT.i2p(o, doReal=doReal)
                    for o in oprs]


            r = SMT.bin_f('(%s %s %s)',SMT.rop2str(op),oprs)

            if doInverse:
                return '(%s %s %s)'%(SMT.rop2str(operator.div),
                                     toreal(Integer(1),doReal),r)
            else:
                return r


    @staticmethod
    def i2p_l(ls,b='and',doBinFormat=True,doReal=False):
        """
        sage: var('y')
        y
        
        sage: from smt import SMT
        
        sage: SMT.i2p_l([3*x + 4/7*x*y == 0, -7*x - 1/2*x^2 >= 0, x - y >= 0],'or')
        '(or (or (= (+ (* (* x y) (/ 4 7)) (* x 3)) 0) (>= (+ (* (* x x) (/ (- 1) 2)) (* x (- 7))) 0)) (>= (+ x (* y (- 1))) 0))'

        sage: SMT.i2p_l([3*x + 4/7*x*y == 0, -7*x - 1/2*x^2 >= 0, x - y >= 0],'or',doReal=True)
        '(or (or (= (+ (* (* x y) (/ 4.00000000000000 7.00000000000000)) (* x 3.00000000000000)) 0.000000000000000) (>= (+ (* (* x x) (/ (- 1.00000000000000) 2.00000000000000)) (* x (- 7.00000000000000))) 0.000000000000000)) (>= (+ x (* y (- 1.00000000000000))) 0.000000000000000))'


        SMT.i2p_l([3*x + 4/7*x*y == 0, -7*x - 1/2*x^2 >= 0, x - y >= 0],'or')
'(or (or (= (+ (* (* x y) (/ 4 7)) (* x 3)) 0) (>= (+ (* (* x x) (/ (- 1) 2)) (* x (- 7))) 0)) (>= (+ x (* y (- 1))) 0))'


        sage: SMT.i2p_l([2*x!=y,x==y],'and')
        '(and (or (> (* x 2) y) (< (* x 2) y)) (= x y))'
        """

        def negFormat(p,doReal):
            lhs = p.lhs()
            rhs = p.rhs()
            return SMT.i2p_l([operator.gt(lhs,rhs),operator.lt(lhs,rhs)],
                             b='or',
                             doReal=doReal)

        if not isinstance(ls,list):
            ls = [ls]

        rs = [negFormat(l,doReal)
              if l.operator()==operator.ne else SMT.i2p(l,doReal=doReal)
              for l in ls]


        return SMT.bin_f('(%s %s %s)',b,rs)




    @staticmethod
    def slfq_format(p,neg=False):
        """
        convert a property p to appropriate qcad/slfq format
        """

        rs = p.negation() if neg else p
        rs = str(rs)
        rs = rs.replace('==','=')
        rs = rs.replace('!=','<>')
        rs = rs.replace('(','')
        rs = rs.replace(')','')
        return rs


    @staticmethod
    def parse_result(smt_result,verbose=1):
        """
        read SMT model results
        
        sage: from smt import SMT

        sage: var('y,z')
        (y, z)
        
        sage: SMT.parse_result('sat\nCurrent scope level is 8.\n%Satisfiable  Variable Assignment: % \n(assert (= x 5))\n(assert (= y 1))\n')
        {y: 1, x: 5}

        sage: SMT.parse_result('sat\nCurrent scope level is 8.\n%Satisfiable  Variable Assignment: % \n(assert (= x (- 5)))\n(assert (= y (- 1)))\n')
        {y: -1, x: -5}

        sage: SMT.parse_result('sat\n(model \n  (define-fun y () Int\n    0)\n  (define-fun z () Int\n    1)\n  (define-fun x () Int\n    0)\n)\n')
        {z: 1, y: 0, x: 0}

        sage: SMT.parse_result("sat\n(model \n  (define-fun x () Int\n    5)\n  (define-fun y () Int\n    1)\n)\n")
        {y: 1, x: 5}

        """

        def _strip(x,stripW):
            for w in stripW:
                while w in x:
                    x = x.replace(w,'')

            return x

        
        smt_result = smt_result.replace('(- ','(-')  #so that (- 5)  becomes (-5)
        

        if 'Satisfiable  Variable Assignment' in smt_result: #cvc3 result
            lines = smt_result.split('\n')
            defines = [_strip(l,['assert','(',')','='])
                       for l in lines if 'assert' in l]
            
        elif 'model' in smt_result:  #z3 result
            lines = _strip(smt_result,['Real\n','Int\n']).split('\n')
            defines = [_strip(l,['define-fun','(',')'])
                       for l in lines if 'define-fun' in l]

        else:
            raise AssertionError('cannot interpret SMT result (%s)'%smt_result)
            
        vs_vals = [l.split() for l in defines]
        vs_vals = [(var(va),Integer(vl)) for va,vl in vs_vals]
        return dict(vs_vals)
    

    @staticmethod
    def smt2_format(vsTypes,formula,verbose=1):
        """
        sage: from smt import SMT
        
        sage: SMT.smt2_format([('x', 'Int'), ('y', 'Int')],'(and (or (or (= (+ x (* y 2)) 2) (= (+ x (* y 2)) 5)) (= (+ x (* y 2)) 7)) (= (+ x y) 6) (or (= x 2) (= x 5)))')
        '(set-logic QF_LIA)\n(declare-fun x () Int)\n(declare-fun y () Int)\n\n\n(assert (and (or (or (= (+ x (* y 2)) 2) (= (+ x (* y 2)) 5)) (= (+ x (* y 2)) 7)) (= (+ x y) 6) (or (= x 2) (= x 5))))\n\n\n(check-sat)\n'

        """

        
        if CM.vall(vsTypes,lambda (v,t): t == 'Int'):
            logic = 'QF_LIA'
        elif CM.vall(vsTypes,lambda (v,t): t == 'Real'):
            logic = 'QF_LRA'
        else:
            raise AssertionError('dont know how to deal with mixed type logic')
            
        declogic = '(set-logic %s)'%logic

        decfuns = '\n'.join(['(declare-fun %s () %s)'%(v,t) 
                              for v,t in vsTypes])
        assertion = '(assert %s)'%formula

        rs = [declogic,
              decfuns,
              '\n',
              assertion,
              '\n',
              '(check-sat)\n']
        
        rs = '\n'.join(rs)
        return rs
        

        

    @staticmethod
    def run(smtCmd,contents,true_kw,retBool=True,getModel=False,verbose=1):
        """
        sage: from smt import SMT
        
        sage: SMT.run('z3 -smt2 -in','(set-logic QF_LRA)\n(declare-fun x () Real)\n(assert (and (> (+ x (- 6)) 0) (not (> (+ x (- 5)) 0))))\n(check-sat)\n',true_kw='unsat',retBool=False,verbose=0)
        (True, 'unsat\n', '')

        sage: SMT.run('z3 -smt2 -in','(set-logic QF_LRA)\n(declare-fun x () Real)\n(assert (and (> (+ x (- 6)) 0) (not (> (+ x (- 7)) 0))))\n(check-sat)\n',true_kw='unsat',retBool=True,verbose=0)
        False

        sage: SMT.run('z3 -smt2 -in','(set-logic QF_LRA)\n(declare-fun x () Real)\n(assert (and (> (+ x (- 6)) 0) (not (> (+ x (- 6)) 0))))\n(check-sat)\n',true_kw='unsat',retBool=False,getModel=True,verbose=0)
        (True, 'unsat\n(error "line 6 column 10: model is not available")\n', '')

        sage: SMT.run('z3 -smt2 -in','(set-logic QF_LRA)\n(declare-fun x () Real)\n(assert (and (> (+ x (- 6)) 0) (not (> (+ x (- 7)) 0))))\n(check-sat)\n',true_kw='unsat',retBool=False,getModel=True,verbose=0)
        (False, 'sat\n(model \n  (define-fun x () Real\n    7.0)\n)\n', '')

        sage: SMT.run('z3 -smt2 -in','(set-logic QF_LRA)\n(declare-fun x () Real)\n(declare-fun y () Real)\n(declare-fun z () Real)\n\n\n(assert (and (= (+ x y) 0) (not (= (+ y z) 0))))\n\n\n(check-sat)\n',true_kw='unsat',retBool=False,getModel=True,verbose=0)
        (False, 'sat\n(model \n  (define-fun y () Real\n    0.0)\n  (define-fun z () Real\n    1.0)\n  (define-fun x () Real\n    0.0)\n)\n', '')

        """
        if getModel == True:
            if 'z3' in smtCmd:
                if '-m' not in smtCmd:
                    smtCmd = smtCmd + ' -m'
                if '(get-model)' not in contents:
                    contents = contents + '\n(get-model)'

                
        if verbose >= 3:
            print 'cmd:', smtCmd
            print 'contents:'
            print contents
            print 'true_kw: ', true_kw

        rs, rs_err = CM.vcmd(cmd=smtCmd,input_=contents,verbose=verbose)

        if verbose >= 4:
            print '***'
            print 'rs_err: '
            print rs_err
            print 'rs: '
            print rs
            print '***'
            
        if rs_err != '':
            is_true = False
        else:
            rs_split = rs.split()
            is_true = true_kw in rs_split
            
        if retBool:
            return is_true
        else:
            return is_true, rs, rs_err



    @staticmethod
    def imply(ps, p, smt_solver, verbose=1):
        """
        #######################
        IDEAL:

        returns true if ps => p

        Using ideals for deduction, does not work with inequality,

        sage: from smt import SMT

        sage: SMT.imply([x-6==0],x*x-36==0,smt_solver='slfq')
        True

        #cvc3 cannot do non-linear 
        sage: SMT.imply([x-6==0],x*x-36==0,smt_solver='cvc3')
        True

        sage: SMT.imply([x-6==0],x-36==0,smt_solver='slfq')
        False

        sage: SMT.imply([x-6==0],x-36==0,smt_solver='cvc3')
        False

        #######################
        CVC:  ps => p iff ps AND ~p  is unsat

        sage: var('x y')
        (x, y)
        
        sage: SMT.imply(x-7>=0,x-6>=0,smt_solver='cvc3',verbose=3)
        cmd: cvc3 -lang smt2
        contents:
        (set-logic QF_LRA)
        (declare-fun x () Real)
        <BLANKLINE>
        <BLANKLINE>
        (assert (and (>= (+ x (- 7)) 0) (not (>= (+ x (- 6)) 0))))
        <BLANKLINE>
        <BLANKLINE>
        (check-sat)
        <BLANKLINE>
        true_kw:  unsat
        True

        sage: SMT.imply([x-6>=0],x-7>=0,smt_solver='cvc3')
        False


        sage: SMT.imply([x-7>=0 , y + 5 >= 0],x + y - 3>=0,smt_solver='cvc3',verbose=3)
        cmd: cvc3 -lang smt2
        contents:
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (declare-fun y () Real)
        <BLANKLINE>
        <BLANKLINE>
        (assert (and (and (>= (+ x (- 7)) 0) (>= (+ y 5) 0)) (not (>= (+ (+ x y) (- 3)) 0))))
        <BLANKLINE>
        <BLANKLINE>
        (check-sat)
        <BLANKLINE>
        true_kw:  unsat
        False


        sage: SMT.imply([x-7>=0 , y + 5 >= 0],x + y -2>=0,smt_solver='cvc3',verbose=3)
        cmd: cvc3 -lang smt2
        contents:
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (declare-fun y () Real)
        <BLANKLINE>
        <BLANKLINE>
        (assert (and (and (>= (+ x (- 7)) 0) (>= (+ y 5) 0)) (not (>= (+ (+ x y) (- 2)) 0))))
        <BLANKLINE>
        <BLANKLINE>
        (check-sat)
        <BLANKLINE>
        true_kw:  unsat
        True

    
        #interesting example
        sage: SMT.imply([x - 2*y >= 0, y-1>=0 ], x - 2 >= 0,smt_solver='cvc3')
        True


        sage: SMT.imply([],x,smt_solver='cvc3')
        False

        ###########
        Z3: ps => p iff ps AND ~p  is unsat
        
        sage: var('x y')
        (x, y)
        
        sage: SMT.imply(x-7>=0,x-6>=0,smt_solver='z3',verbose=3)
        cmd: z3 -smt2 -in
        contents:
        (set-logic QF_LRA)
        (declare-fun x () Real)
        <BLANKLINE>
        <BLANKLINE>
        (assert (and (>= (+ x (- 7)) 0) (not (>= (+ x (- 6)) 0))))
        <BLANKLINE>
        <BLANKLINE>
        (check-sat)
        <BLANKLINE>
        true_kw:  unsat
        True

        sage: SMT.imply([x-6>=0],x-7>=0,smt_solver='z3')
        False


        sage: SMT.imply([x-7>=0 , y + 5 >= 0],x + y - 3>=0,smt_solver='z3',verbose=3)
        cmd: z3 -smt2 -in
        contents:
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (declare-fun y () Real)
        <BLANKLINE>
        <BLANKLINE>
        (assert (and (and (>= (+ x (- 7)) 0) (>= (+ y 5) 0)) (not (>= (+ (+ x y) (- 3)) 0))))
        <BLANKLINE>
        <BLANKLINE>
        (check-sat)
        <BLANKLINE>
        true_kw:  unsat
        False


        sage: SMT.imply([x-7>=0 , y + 5 >= 0],x + y -2>=0,smt_solver='z3',verbose=3)
        cmd: z3 -smt2 -in
        contents:
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (declare-fun y () Real)
        <BLANKLINE>
        <BLANKLINE>
        (assert (and (and (>= (+ x (- 7)) 0) (>= (+ y 5) 0)) (not (>= (+ (+ x y) (- 2)) 0))))
        <BLANKLINE>
        <BLANKLINE>
        (check-sat)
        <BLANKLINE>
        true_kw:  unsat
        True

    
        #interesting example
        sage: SMT.imply([x - 2*y >= 0, y-1>=0 ], x - 2 >= 0,smt_solver='z3')
        True


        sage: SMT.imply([],x,smt_solver='z3')
        False

        ########
        QCAD:  ps => p iff ~ps OR p is true

        #non-linear

        sage: var('x y')
        (x, y)
        sage: SMT.imply([x-7>=0 , y + 5 >= 0],x + y -2>=0,smt_solver='slfq')
        True

        sage: SMT.imply([x^2 - 9 >= 0, x >= 0], x - 3 >= 0,smt_solver='slfq',verbose=3)
        cmd: slfq -q
        contents:
        (x^2 - 9 < 0 or  x < 0)
        or
        (x - 3 >= 0)
        true_kw:  TRUE
        True


        sage: SMT.imply([1/2*x**2 - 3/28*x + 1 >= 0],1/20*x**2 - 9/20*x + 1 >= 0,smt_solver='slfq',verbose=3)
        cmd: slfq -q
        contents:
        (1/2*x^2 - 3/28*x + 1 < 0)
        or
        (1/20*x^2 - 9/20*x + 1 >= 0)
        true_kw:  TRUE
        False


        sage: SMT.imply([1/20*x**2 - 9/20*x + 1 >= 0],1/2*x**2 - 3/28*x + 1 >= 0,smt_solver='slfq',verbose=3)
        cmd: slfq -q
        contents:
        (1/20*x^2 - 9/20*x + 1 < 0)
        or
        (1/2*x^2 - 3/28*x + 1 >= 0)
        true_kw:  TRUE
        True

        sage: SMT.imply([x-6==0],x*x-36==0,smt_solver='slfq')
        True


        sage: SMT.imply([x + 7>=0 , y + 5 >= 0],\
        x*y + 35 >=0,smt_solver='slfq',verbose=4)
        cmd: slfq -q
        contents:
        (x + 7 < 0 or  y + 5 < 0)
        or
        (x*y + 35 >= 0)
        true_kw:  TRUE
        ***
        rs_err: 
        <BLANKLINE>
        rs: 
        [ y x + 35 >= 0 \/ y + 5 < 0 \/ x + 7 < 0 ]
        <BLANKLINE>
        ***
        False

        #linear
        sage: SMT.imply([x-6>=0],x-7>=0,smt_solver='slfq')
        False

        sage: SMT.imply([x-7>=0],x-6>=0,smt_solver='slfq')
        True

        # sage: SMT.imply([x-6>=0],x-7.2>=0,smt_solver='slfq')
        AssertionalError: fractions ...

        """

        if CM.is_none_or_empty(ps):
            return False

        assert smt_solver == 'cvc3' or smt_solver == 'z3' or smt_solver == 'slfq',\
            'E: unrecognized SMT prog: %s'%smt_solver
            
        if not isinstance(ps,list):
            ps=[ps]

        #Generates the query ps => p in several SMT Formats
        if smt_solver == 'slfq':
            """
            not ps or p 
            : true ->  ps => p
            : false -> ps /=> p
            """

            assert '.' not in str(ps) + str(p), \
                'E: fractions (e.g., 1.8, 0.7) are not allowed in SLFQ!'

            ps = ' or  '.join([SMT.slfq_format(p_,neg=True) for p_ in ps])
            p = SMT.slfq_format(p,neg=False)
            formula =  '(' + ps + ')' + '\nor\n' + '(' + p + ')'

        else: #'cvc3' or 'z3'
            vs = Miscs.get_vars(ps+[p])
            vsTypes = [(str(v),'Real') for v in vs]
            a = SMT.i2p_l(ps)
            b = SMT.i2p(p)
            
            formula = "(and %s (not %s))"%(SMT.i2p_l(ps),SMT.i2p(p))
            
            formula = SMT.smt2_format(vsTypes,formula)
            
        
        #run the SMT solver
        if smt_solver == 'cvc3':
            cmd = 'cvc3 -lang smt2'
            kw = 'unsat'
        elif smt_solver == 'z3':
            cmd = 'z3 -smt2 -in'
            kw = 'unsat'
        else : #slfq
            cmd = 'slfq -q'
            kw= 'TRUE'

        rs = SMT.run(smtCmd=cmd,contents=formula,true_kw=kw,verbose=verbose)
                        
        return rs






