    def replace_subtree(self, root_name, replace_tree):
        """
        Replace the subtree whose root is root_name in self with the new tree
        """
        
        if self.is_leaf():
            return self
        
        if self.root.name == root_name:
            return replace_tree
        else:
            return Tree(Node(name=self.root.name,nchildren=self.root.nchildren),
                        children = [c.replace_subtree(root_name,replace_tree) for 
                                    c in self.children])



    @staticmethod
    def get_roots(tree,roots=[],verbose=1):
        """
        DEPRECATE
        EXAMPLES:

        sage: Miscs.get_roots(None)
        []
        sage: Miscs.get_roots({'root':'A','children':[{'root':'B','children':[None,None]},{'root':'C','children':[None,{'root':'G','children':[None,None]}]}]})
        ['A', 'B', 'C', 'G']

        sage: Miscs.get_roots({'root': 'xor', 'children': [{'root': 'a', 'children': [x*x]}, {'root': 'b', 'children': [x+1]}]})
        ['xor', 'a', 'b']

        """
        if isinstance(tree,dict) and 'root' in tree:
            roots_tc = [Miscs.get_roots(tc,roots,verbose=verbose)
                        for tc in tree['children']]

            roots = [tree['root']] + flatten(roots_tc)
            return roots
        else:
            return roots





    @staticmethod
    def getLeaves(t,verbose=1):
        """
        DEPRECATED

        EXAMPLES:

        sage: Miscs.getLeaves(None)
        [(None, None, [])]

        sage: Miscs.getLeaves({'root': 'add', 'children': [{'root': 'C', 'children': [None]}, {'root': 'D', 'children': [None]}]})
        [({'root': 'C', 'children': [None]}, 0, ['add', 0, 'C', 0]), 
        ({'root': 'D', 'children': [None]}, 0, ['add', 1, 'D', 0])]
        """

        def _getLeaves(t,p,idx,tid):

            if t is None:  #leaf
                return [(p,idx,tid)]
            else:
                children = t['children']
                results = [_getLeaves(child, t, idx_, tid+[t['root'],idx_]) 
                           for idx_,child in Miscs.senumerate(children)]

                results = flatten(results,list)
                return results


        return _getLeaves(t,p=None,idx=None,tid=[])






    @staticmethod
    def tree2str(tree,leafInfo=None,verbose=1):
        """
        DEPRECATE

        EXAMPLES:

        sage: Miscs.tree2str({'root': 'a', 'children': [{'root': 'xor_xor', 'children': [{'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}]}]})
        'a[xor_xor(c[None],c[None],c[None])]'

        sage: Miscs.tree2str({'root': 'a', 'children': [{'root': 'b', 'children': [{'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}]}]})
        'a[b[c[None]][c[None]][c[None]]]'

        sage: Miscs.tree2str({'root': 'a', 'children': [{'root': 'xor_xor', 'children': [{'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}]}]},leafInfo='this is a leaf')
        'a[xor_xor(c[this is a leaf],c[this is a leaf],c[this is a leaf])]'
        """

        try:
            childrenStr= [Miscs.tree2str(c,leafInfo,verbose=verbose) 
                          for c in tree['children']]
            try:
                ExtFun.getFun(tree['root'])
                res = '(%s)'%(','.join(childrenStr))
            except KeyError:
                res = '%s'%(''.join(['[%s]'%cs for cs in childrenStr]))

            return tree['root']+res

        except Exception:
            if leafInfo is None:
                return str(tree)
            elif isinstance(leafInfo,dict):
                return str((tree)(leafInfo))
            else:
                return leafInfo


    @staticmethod
    def aexp2str(arr_exp,leafInfo=None,do_lambda_format=False,verbose=1):
        """
        DEPRECATE

        do_lambda_format=True: returns the lambda format


        EXAMPLES:

        sage: Miscs.aexp2str(({'root':'rvu','children':[None]}, {'root': 'a', 'children': [{'root': 'xor_xor', 'children': [{'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}]}]}))
        'rvu[i1] == a[xor_xor(c[(i1)_],c[(i1)_],c[(i1)_])]'

        sage: Miscs.aexp2str(({'root':'rvu','children':[None]}, {'root': 'a', 'children': [{'root': 'xor_xor', 'children': [{'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}]}]}),do_lambda_format=True)
        'lambda rvu,a,xor_xor,c,i1: rvu[i1] == a[xor_xor(c[(i1)_],c[(i1)_],c[(i1)_])]'

        sage: Miscs.aexp2str(({'root':'rvu','children':[None,None]}, {'root': 'a', 'children': [{'root': 'xor_xor', 'children': [{'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None,None]}]}]}),do_lambda_format=True)
        'lambda rvu,a,xor_xor,c,i1,i2: rvu[i1][i2] == a[xor_xor(c[(i1,i2)_],c[(i1,i2)_],c[(i1,i2)_][(i1,i2)_])]'

        sage: Miscs.aexp2str(({'root':'rvu','children':[None,None]}, {'root': 'a', 'children': [{'root': 'xor_xor', 'children': [{'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None,None]}]}]}))
        'rvu[i1][i2] == a[xor_xor(c[(i1,i2)_],c[(i1,i2)_],c[(i1,i2)_][(i1,i2)_])]'

        sage: Miscs.aexp2str(({'root':'rvu','children':[None]}, {'root': 'a', 'children': [{'root': 'xor_xor', 'children': [{'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}]}]}),do_lambda_format=True)
        'lambda rvu,a,xor_xor,c,i1: rvu[i1] == a[xor_xor(c[(i1)_],c[(i1)_],c[(i1)_])]'

        sage: Miscs.aexp2str(({'root':'rvu','children':[None]}, {'root': 'a', 'children': [{'root': 'xor_xor', 'children': [{'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}, {'root': 'c', 'children': [None]}]}]}),do_lambda_format=False)
        'rvu[i1] == a[xor_xor(c[(i1)_],c[(i1)_],c[(i1)_])]'

        sage: var('y')
        y
        sage:  Miscs.aexp2str(({'root':'rvu','children':[x+5]}, {'root': 'a', 'children': [{'root': 'xor_xor', 'children': [{'root': 'c', 'children': [7-y]}, {'root': 'c', 'children': [x-y]}, {'root': 'c', 'children': [x+y]}]}]}),do_lambda_format=True,leafInfo={x:5,y:7})
        'lambda rvu,a,xor_xor,c,i1: rvu[i1] == a[xor_xor(c[0],c[-2],c[12])]'

        """
        lhs,rhs  = arr_exp
        lhs_nargs = len(lhs['children'])
        lhs_idxs = [(i+1) for i in srange(lhs_nargs)]
        lhs_idxs_indexFormat = ''.join(['[i%s]'%li for li in lhs_idxs]) #[i][j]
        lhs_idxs_argsFormat = ','.join(['i%s'%li for li in lhs_idxs])  #i,j


        if leafInfo is None:
            rhs_idxs = "(%s)_"%lhs_idxs_argsFormat
            rhs = Miscs.tree2str(rhs,leafInfo=rhs_idxs,verbose=verbose)
        else:
            assert isinstance(leafInfo,dict)
            rhs = Miscs.tree2str(rhs,leafInfo=leafInfo,verbose=verbose)


        result = '%s%s == %s'%(lhs['root'],lhs_idxs_indexFormat,rhs)

        if do_lambda_format:
            lhs_idxs_ = ','.join(['i%s'%li for li in lhs_idxs])
            nodes = [lhs['root']]  + list(set(Miscs.get_roots(arr_exp[1])))
            lambda_ = 'lambda %s,%s' %(','.join(nodes),lhs_idxs_argsFormat)
            result= '%s: %s'%(lambda_,result)

        return result



    @staticmethod
    def gt(root,availChildren,vss=None,data=None,blacklist={},verbose=1):
        """

        DEPRECATE


        EXAMPLES:

        #cannot do this one
        res = Miscs.gt('a',['b','c','d','e'],{'a':2,'b':1,'c':1,'d':1,'e':1},{});len(res)

        #old gt function, data argument is no longer compatiable
        #sage: res = Miscs.gt('xor',availChildren=['i0','i1','i2','i3','st'],data={'xor':2,'i0':1,'i1':1,'i2':1,'i3':1,'st':2}, blacklist={'i0':['i1','i2','i3'],'i1':['i0','i2','i3'],'i2':['i0','i1','i3'],'i3':['i0','i1','i2']});len(res)
        #8836

        sage: Miscs.gt('B',availChildren=['C','D'],vss=[(8,),(15,),(7,)],data={'A': {8: [(0,)], 7: [(2,)], 15: [(1,)]}, 'C': {8: [(2, 6)], 10: [(3, 7), (8, 2)], 3: [(1, 2)], 4: [(0, 4)], 2: [(2, 0), (1, 7)]}, 'B': {8: [(10,), (4,)], 7: [(2,)], 15: [(8,), (3,)]}, 'E': {0: [(15,)], 6: [(3,)], 7: [(18,)]}, 'D': {8: [(7,)], 1: [(9,)], 2: [(8,)], 3: [(5,)]}})        
        [
        {'root': 'B', 'children': [{'root': 'C', 'children': [{'root': 'D', 'children': [{'root': 'B', 'children': [None]}]}, None]}]}, 
        {'root': 'B', 'children': [{'root': 'C', 'children': [{'root': 'D', 'children': [None]}, None]}]}, 
        {'root': 'B', 'children': [{'root': 'C', 'children': [None, None]}]}, 
        {'root': 'B', 'children': [None]}]

        todo:  commutative function

        """
        rootData = data[root]
        nChildren = len(rootData[rootData.keys()[0]][0])

        if vss is not None:
            childrenVss = Miscs.reach(vss,rootData)
            if childrenVss is None:
                #if none of the list in values is subset of rootData,
                #then no tree whose root='root' generated
                return []
        else:
            childrenVss = [None]*nChildren

        if availChildren:
            children = availChildren + [None]

            children = [c for c in children
                        if root not in blacklist or c not in blacklist[root]]

            #recursive call
            _gt = lambda root_, availChildren_, vss_, : \
                None if root_ is None else \
                Miscs.gt(root=root_,availChildren=availChildren_,
                         vss=vs,data=data,blacklist=blacklist,verbose=verbose)


            children = [[_gt(c,list(set(availChildren)-set([c])),vs) 
                          for c in children]
                          for vs in childrenVss]
            children = [flatten(c) for c in children]

            if len(children) != nChildren:
                print 'root', root
                print 'vss',vss

                print 'nchildren', nChildren
                print 'len(children)',len(children)
                print 'data', rootData
                assert False

            combs = CartesianProduct(*children)
            res = [{'root':root, 'children':c} for c in combs]

        else:  #if availChildren == [] then all children are Leaves
            res= [{'root':root,'children':[None]*nChildren}]

        return res

    @staticmethod
    def gen_trees(nodes,vss,data,blacklist,verbose=1):
        """
        DEPRECATE

        From given nodes such as [a,b,c], returns all possible trees, e.g. [{a,[b,c],{a,[c,b]}},{b,[a,c]} ..
        Also performs some prelim pruning based on trace data

        EXAMPLES:

        #todo: check me
        #sage: res = Miscs.gen_trees(['a','b','c'],{'a':1,'b':2,'c':3},{});len(res)
        477

        """
        _gt = lambda node:\
            Miscs.gt(root=node,
                     availChildren=list(set(nodes)-set([node])),
                     vss=vss,
                     data=data,
                     blacklist=blacklist,
                     verbose=verbose)

        trees = [ _gt(node) for node in nodes]
        trees = flatten(trees)
        return trees


    @staticmethod
    def _f(ls,op):
        """
        DEPRECATE
        """
        if CM.vany(ls,lambda l: l is None) or ls == []:
            return None

        rs = [SMT_Z3.to_z3exp(l,is_real=False) \
                  if isinstance(l,CM.sage_expr) \
                  else l
              for l in ls]

        if len(rs) == 1:
            rs = rs[0]
        else:
            rs = z3.And(rs) if op == 'and' else z3.Or(rs)
        
        return rs


    @staticmethod
    def genTemplate(aexp,idxs_vals=None,special=False,verbose=1):
        """
        DEPRECATE

        special = True then it means we only have 1 data to compare against
        thus if the pass in indices of the leaves are 0's  , the result will be  z + 0*i = 0 
        which then just gives z = 0, doesn't contribute to anything if we have only 1 data.
        Thus special flag turns the result z + 0*i = 0 into z = 0 and i = 1.

        EXAMPLES:

        sage: NestedArray.genTemplate(({'root':'R','children':[None,None,None]},{'root': 'add', 'children': [{'root': 'C', 'children': [None]}, {'root': 'D', 'children': [None]}]}),verbose=1)
        ({'root': 'R', 'children': [None, None, None]}, {'root': 'add', 'children': [{'root': 'C', 'children': [_add_0_C_0__i1*i1 + _add_0_C_0__i2*i2 + _add_0_C_0__i3*i3 + _add_0_C_0__i0]}, {'root': 'D', 'children': [_add_1_D_0__i1*i1 + _add_1_D_0__i2*i2 + _add_1_D_0__i3*i3 + _add_1_D_0__i0]}]})


        sage: NestedArray.genTemplate(({'root':'R','children':[None,None]},{'root': 'add', 'children': [{'root': 'C', 'children': [None]}, {'root': 'D', 'children': [None]}]}),verbose=1)
        ({'root': 'R', 'children': [None, None]}, {'root': 'add', 'children': [{'root': 'C', 'children': [_add_0_C_0__i1*i1 + _add_0_C_0__i2*i2 + _add_0_C_0__i0]}, {'root': 'D', 'children': [_add_1_D_0__i1*i1 + _add_1_D_0__i2*i2 + _add_1_D_0__i0]}]})

        sage: NestedArray.genTemplate(({'root':'R','children':[None,None]},{'root': 'add', 'children': [None,None]}),idxs_vals=[0,0],special=True)
        ({'root': 'R', 'children': [None, None]}, {'root': 'add', 'children': [{'coef': _add_0__i0, 'first_idx': _add_0__i1}, {'coef': _add_1__i0, 'first_idx': _add_1__i1}]})

        sage: NestedArray.genTemplate(({'root':'R','children':[None,None]},{'root': 'add', 'children': [None,None]}),idxs_vals=[0,0],special=False)
        ({'root': 'R', 'children': [None, None]}, {'root': 'add', 'children': [_add_0__i0, _add_1__i0]})

        """
        #special implies idxs=(0,..,0)
        assert not special or CM.vall(idxs_vals,lambda x: x==0)

        #idxs_vals is None implies special=False
        assert idxs_vals is not None or not special

        lhs,rhs_ = aexp
        lhs_nargs = len(lhs['children'])

        rhs = deepcopy(rhs_)  #make a copy

        leaves = Miscs.getLeaves(rhs,verbose=verbose)

        leaves = [(p,idx,tid) for p,idx,tid in leaves if p is not None]
        print 'gh'
        print [(str(p),idx,tid) for p,idx,tid in leaves if p is not None]

        if idxs_vals is None:
            ts = [1]+[var('i%d'%(i+1)) for i in srange(lhs_nargs)]
        else:
            ts = [1]+ list(idxs_vals)
        print 'ts',ts

        for p,idx,tid in leaves:
            prefix = '_%s__i'%'_'.join(map(str,tid))
            if special:
                rs = {'first_idx':var(prefix+str(1)),'coef':var(prefix+str(0))}
            else:
                rs = Miscs.gen_template(ts,rv=None,prefix=prefix,verbose=verbose)
            print 'rs',rs

            p['children'][idx]= rs
            print 'p',p
        return (lhs,rhs)



    @staticmethod
    def gen_blacklist(xinfo,verbose=1):
        """
        DEPRECATE

        Takes advantage of user inputs to reduce the number of generated nestings

        EXAMPLES:

        sage: NestedArray.gen_blacklist({'All':['R','A','B','D','E','xor','g'],'Input':['A','B'],'Output':['R'],'Global':[],'Const':[],'ExtFun':['xor'],'Global':['g']})
        {'A': ['R', 'A', 'B', 'D', 'E', 'xor', 'g'], 'R': ['R', 'A', 'B', 'D', 'E', 'xor', 'g', None], 'B': ['R', 'A', 'B', 'D', 'E', 'xor', 'g'], 'xor': [None], 'g': [None]}
        
        """

        allVars    = xinfo['All']
        inputVars  = xinfo['Input']
        outputVars = xinfo['Output']
        globalVars = xinfo['Global']
        constVars  = xinfo['Const']
        extFuns    = [x for x in xinfo['ExtFun']]

        #Inputs must be leaves
        #e.g., a[i] = x[y[i']] is not possible
        #e.g., a[i] = xor[x[i'][y[i']]
        inputsLeaves = [{inp:allVars} for inp in inputVars]

        #Const must be leaves
        constLeaves = [{c:allVars} for c in constVars]

        #Extfuns are never leaves
        #e.g.,  r[i] = a[b[xor[i'][i']]]  is not possible
        extfunsNotLeaves = [{ef:[None]} for ef in extFuns]

        #Globals are never leaves
        globalsNotLeaves = [{gv:[None]} for gv in globalVars]

        #Outputs should never be part of the tree
        outputsNotInTree = [{oup:allVars + [None]} for oup in outputVars]

        ds = inputsLeaves+constLeaves+extfunsNotLeaves+\
            globalsNotLeaves+outputsNotInTree
        res = CM.merge_dict(ds)
        return res


    @staticmethod
    def prune_aexps(ae,xinfo,verbose=1):
        """
        DEPRECATE
        Returns only potential nesting by pruning out invalid ones
        e.g., those that do not contain the input variables
        """
        
        _,rh = ae
        roots = Miscs.get_roots(rh,verbose=verbose)
        inputVars = xinfo['Input']
        #all inputs must be in rhs

        rs = CM.vall(inputVars, lambda iv: iv in roots)
        return rs

    @staticmethod
    def gen_aexps(arrs,data,xinfo,verbose=1):
        """
        DEPRECATE
        arrs = [a,b,c]
        returns a=allpostrees(b,c)  , b = allpostrees(a,b)  , etc
        """

        blacklist = NestedArray.gen_blacklist(xinfo,verbose=verbose)

        def _gt(arrs,vss):
            assert CM.vall(vss, lambda v: not CM.is_iterable(v))

            #note that gen_trees also do pruning based on traces
            rs =  Miscs.gen_trees(arrs,vss=map(lambda v: tuple([v]),vss),data=data,
                                  blacklist=blacklist,verbose=verbose)
            return rs

        _gl = lambda lh, dim: {'root':lh,'children':[None]*dim}

        if xinfo['Output']:
            #x = a[b[...]], x in output vars and a,b not in output vars
            setDiff = list(set(arrs) - set(xinfo['Output']))

            aexps = [[(_gl(lh,xinfo['ZDims'][lh]),rh)
                      for rh in _gt(setDiff,data[lh].keys())]
                      for lh in xinfo['Output']]

        else:
            aexps= [[(_gl(lh,xinfo['ZDims'][lh]),rh)
                      for rh in _gt(list(set(arrs)-set([lh])),data[lh].keys())]
                    for lh in arrs]
        
        aexps = flatten(aexps,list)


        #filter out unlikely array expressions
        aexps = [ae for ae in aexps
                 if NestedArray.prune_aexps(ae,xinfo,verbose=verbose)]

        if verbose >= 1:
            print '* gen_aexps [%s]: %d expressions generated'\
                %(','.join(map(str,arrs)),len(aexps))

            if verbose >= 2:
                arrStrs = ['%d. %s'%(i,Miscs.aexp2str(ae,verbose=verbose))
                           for i,ae in Miscs.senumerate(aexps)]
                print '\n'.join(arrStrs)

        return aexps


    @staticmethod
    def peelme(aexp,data,verbose=1):
        """
        Go through each nesting (aexp) and generate SMT query
        
        EXAMPLES:
        
        #a[i] = b[c[i+5]]
        sage: smtres = NestedArray.peelme(({'root':'A','children':[None]},{'root':'B','children':[{'root':'C','children':[None]}]}),{'A':{71:[(0,)],74:[(1,)],81:[(2,)]},'B':{71:[(5,),(7,)],74:[(6,),(8,)],81:[(17,)]},'C':{0:[(0,),(3,)],9:[(1,),(8,)],7:[(2,),(5,)],1:[(4,)],8:[(6,)],17:[(7,)]}},verbose=1); print '\n'.join(smtres)
        lambda A,C,B,i1: A[i1] == B[C[i1 + 5]]


        #a[i,j] = add[c[i+2],d[j+1]]
        sage: smtres = NestedArray.peelme(({'root':'A','children':[None,None]},{'root':'add','children':[{'root':'C' , 'children':[None]},{'root':'D','children':[None]}]}), {'C':{0:[(0,)],17:[(1,)],8:[(2,)],3:[(3,),(4,)]},'D':{1:[(0,)],9:[(1,),(3,)],0:[(2,)]},'add':{17:[(8,9),(17,0)],8:[(8,0)],12:[(3,9),(0,12)],3:[(3,0)]},'A':{17:[(0,0)],8:[(0,1)],12:[(1,0)],3:[(1,1)]}});print '\n'.join(smtres)
        lambda A,add,C,D,i1,i2: A[i1][i2] == add(C[i1 + 2],D[i2 + 1])
        lambda A,add,C,D,i1,i2: A[i1][i2] == add(C[i1 + 2],D[-i2 + 3])
        lambda A,add,C,D,i1,i2: A[i1][i2] == add(C[2*i1 + 2],D[-i2 + 3])
        lambda A,add,C,D,i1,i2: A[i1][i2] == add(C[2*i1 + 2],D[i2 + 1])  


        #todo: check me,  forall i. i%3==0 , a[i]=b[c[i-2]]
        #sage: smtres = NestedArray.peelme(({'root':'A','children':[None]},{'root':'B','children':[{'root':'C','children':[None]}]}),{'A':{0: [(2,)], 71: [(3,)], 8: [(0,)], 74: [(6,)], 171: [(5,)], 15: [(8,)], 81: [(9,)], -1: [(1,)], 10: [(7,)], -2: [(4,)]},'B':{17: [(8,)], 71: [(3,), (6,)], 8: [(7,)], 9: [(0,)], 74: [(5,)], 15: [(4,)], 81: [(1,)], -1: [(2,)]},'C':{1: [(7,)], 5: [(4,)], 6: [(1,)], 8: [(2,)], 15: [(5,)], 17: [(3,)], 19: [(6,)], 21: [(8,)], -1: [(0,)]}},verbose=1); smtres
        'A[i1] = B[C[i1 - 2]]'
        """


        _gen_template = lambda iv,sp: \
            NestedArray.genTemplate(aexp,idxs_vals=iv,
                                    special=sp,verbose=verbose)

        lhs,_ = aexp
        lhs_name = lhs['root']
        vi = [[(v,ids) for ids in idxs] for v,idxs in data[lhs_name].items()]
        vi = flatten(vi,list)

        if verbose >= 2:
            print 'vi: ', vi

        sts = [_gen_template(ids,sp=len(vi)==1)[1] for _,ids in vi]
        print len(sts)
        print '\n'.join(map(str,sts))
        CM.pause('gh2')
        #apply reachability analysis (peel) to each element of LHS
        formula = [NestedArray.reachability(v,rh,data,verbose=verbose) 
                   for (v,_),rh in zip(vi,sts)]
        print 'formula', formula
        formula = NestedArray._f(formula,'and')
        print 'formula1', formula

        if formula is None:
            return None

        s = z3.Solver()
        s.add(formula)

        ms = SMT_Z3.get_models(s,k=10)
        if len(ms) == 0: #no model, formula is unsat, i.e. no relation
            return None

        ds = [SMT_Z3.get_constraints(m,result_as_dict=True)
              for m in ms]
        print ds
        #generate the full expression
        template = _gen_template(None,False)
        #print template
        rs = [Miscs.aexp2str(template,leafInfo=d,do_lambda_format=True) 
              for d in ds]

        return rs


    @staticmethod
    def reachability(v,nesting,data,verbose=1):
        """
        EXAMPLES:

        sage: NestedArray.reachability(17,{'root':'add','children':[{'root':'C' , 'children':[{'root':'_add_0_C_','children':[100,200]}]},{'root':'D','children':[{'root':'_add_1_D_','children':[100,200]}]}]}, {'C':{0:[(0,)],17:[(1,)],8:[(2,)],3:[(3,),(4,)]},'D':{1:[(0,)],9:[(1,),(3,)],0:[(2,)]},'add':{17:[(8,9),(17,0)],8:[(8,0)],12:[(3,9),(0,12)],3:[(3,0)],'A':{17:[(0,0)],8:[(0,1),(2,1)],12:[(1,0)],3:[(1,1),(2,0)]}}})

        sage: var('_B_0_C_0__i0 _B_0_C_0__i1')
        (_B_0_C_0__i0, _B_0_C_0__i1)
        sage: v = 81
        sage: nesting = a = {'root': 'B', 'children': [{'root': 'C', 'children': [_B_0_C_0__i0 + 2*_B_0_C_0__i1]}]}
        sage: data = {'A': {81: [(2,)], 74: [(1,)], 71: [(0,)]}, 'C': {0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]}, 'B': {81: [(17,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}}

        sage: NestedArray.reachability(v,nesting,data)
        _B_0_C_0__i0 + _B_0_C_0__i1*2 == 7
        

        sage: data = {'A': {81: [(2,)], 74: [(1,)], 71: [(0,)]}, 'C': {0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]}, 'B': {81: [(17,), (9,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}}

        sage: NestedArray.reachability(v,nesting,data)
        Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 7,
        Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 1,
        _B_0_C_0__i0 + _B_0_C_0__i1*2 == 8))

        """

        assert isinstance(nesting,CM.sage_expr)\
            or isinstance(nesting,dict)

        if isinstance(nesting,CM.sage_expr):
            #when reach the leaf, return leaf = index
            return nesting == v

        elif isinstance(nesting,dict) and 'first_idx' in nesting: 
            #special case {'first_idx':i,'coef':z}
            if v == 0:
                t0 = nesting['coef'] == 0
                t1 = nesting['first_idx'] == 1
                return NestedArray._f([t0,t1],'and')
            else:
                return nesting['coef'] == v
        else:
            try:
                idxs = data[nesting['root']][v]
            except KeyError: #not reachable, no rel
                return None

            orRs = []
            for idx in idxs:
                andRs = []
                for v_,a_ in zip(idx,nesting['children']):
                    p_ = NestedArray.reachability(v_,a_,data,verbose=verbose)

                    if p_ is None:
                        andRs = None
                        break
                    andRs.append(p_)


                if andRs is not None:
                    assert len(andRs)>0
                    andRs = NestedArray._f(andRs,'and') 
                    orRs.append(andRs)

            orRs = NestedArray._f(orRs,'or')
            return orRs



        #arr_dims = [(k,len(c.values()[0][0])) for k,c in tc.items()] #todo: remove when don
        #arr_dims_d = {'ZDims': dict(arr_dims)} #todo: remove when done
        
        #self.xinfo = CM.merge_dict([xinfo,arr_dims_d])   #todo: remove when done
        #print CM.dict2str(self.xinfo)


class Node(object):
    
    def __init__(self, name, nchildren, is_ordered=True):
        """
        sage: var('y')
        y

        sage: print Node(name=x+y,nchildren=0)
        x + y

        sage: print Node(name='a',nchildren=2)
        a

        sage: print Node(name={'coef': x, 'first_idx': y},nchildren=0)
        {'first_idx': y, 'coef': x}

        sage: Node(name=156,nchildren=2)
        Traceback (most recent call last)
        ...
        AssertionError: Non str name must be a leaf (name=156, nchildren=2)

        """
        assert CM.imply(not isinstance(name,str), nchildren ==0), \
            'Non str name must be a leaf (name=%s, nchildren=%d)'%(name, nchildren)
        
        assert nchildren >= 0
        self.name = name  #could be anything
        self.nchildren = nchildren

        self.is_ordered = is_ordered
        
    def __str__(self, leaf_content=None, print_structure=False):
        """
        Return the string representation of node.

        - leaf_content: gives the leaf_content of leaf node, instead of the node's name

        - print_structure: full details of how the node is constructed. 
        If this flag is set, then leaf_content will be ignored.

        EXAMPLES:
        sage: print Node(x,0,False).__str__(leaf_content={x:x^2+7})
        x^2 + 7

        sage: print Node(x,0,False).__str__(print_structure=True)
        Node(name=x, nchildren=0, is_ordered=False)

        sage: print Node('x',0,False).__str__(print_structure=True)
        Node(name='x', nchildren=0, is_ordered=False)

        """
        name = self.name

        if self.is_leaf() and leaf_content is not None:
            if isinstance(leaf_content,dict):
                if isinstance(name,CM.sage_expr):
                    return str(name(leaf_content))
                else:
                    return str(name)
            else:
                return str(leaf_content)
        else:
            if print_structure:
                s = "Node(name=%s, nchildren=%d, is_ordered=%s)"
                return s%("'%s'"%name if isinstance(name,str) else name,
                          self.nchildren,self.is_ordered)
            else:
                return str(name)

    def is_leaf(self):
        return self.nchildren == 0
    
    @staticmethod
    def leaf_node(): 
        return Node('leaf', nchildren=0, is_ordered=False)
    

class Tree(object):
    
    def __init__(self, root, children):

        assert isinstance(root,Node)
        assert isinstance(children,list) and \
            CM.vall(children,lambda c: isinstance(c, Tree))

        self.root = root
        self.children = children
    

    def get_str_formats(self):
        """
        Note that this function should only be used on tree with exactly 1 level, 
        e.g. A[leaf][leaf].
        """
        assert CM.vall(self.children, lambda c: c.is_leaf())

        idxs = [(i+1) for i in srange(self.root.nchildren)]
        iformat = ''.join(['[i%s]'%li for li in idxs]) #[i][j]
        aformat = ','.join(['i%s'%li for li in idxs])  #i,j
        return idxs, iformat, aformat

    def __str__(self, leaf_content=None, print_structure=False):
        """
        sage: Tree(Node('leaf',nchildren=0),children=[]).__str__(leaf_content='hi')
        'hi'

        sage: Tree(Node('a',nchildren=1), \
        children=[Tree(Node('x',nchildren=2), \
        children=[Tree(Node('c',nchildren=1), \
        children=[Tree(Node('leaf',nchildren=0),children=[])]), \
        Tree(Node('d',nchildren=1), \
        children=[Tree(Node('leaf',nchildren=0),children=[])])])]).__str__(leaf_content='my info')
        'a[x[c[my info]][d[my info]]]'

        sage: Tree(Node('a',nchildren=1), \
        children=[Tree(Node('x',nchildren=2), \
        children=[Tree(Node('c',nchildren=1), \
        children=[Tree(Node('leaf',nchildren=0),children=[])]), \
        Tree(Node('d',nchildren=1), \
        children=[Tree(Node('leaf',nchildren=0),children=[])])])]).__str__()
        'a[x[c[leaf]][d[leaf]]]'

        sage: Tree(Node('a',nchildren=1),
        children=[Tree(Node('x',nchildren=2),
        children=[Tree(Node('c',nchildren=1),
        children=[Tree(Node(x,nchildren=0),children=[])]),
        Tree(Node('d',nchildren=1),
        children=[Tree(Node(x+x^2,nchildren=0),children=[])])])]).__str__(leaf_content={x:5})
        'a[x[c[5]][d[30]]]'

        """
        children = [c.__str__(leaf_content=leaf_content, 
                              print_structure=print_structure) 
                    for c in self.children]

        root = self.root.__str__(leaf_content=leaf_content, 
                                 print_structure=print_structure)
        
        if print_structure:
            rs = 'Tree(root=%s,children=[%s])'%(root,','.join(children))
        else:
            try:
                ExtFun.getFun(self.root.name)
                rs = '(%s)'%(','.join(children))
            except KeyError:
                rs = ''.join(['[%s]'%c for c in children])
            rs = '%s%s'%(root,rs)
        return rs

    def is_leaf(self):
        return self.root.is_leaf()

    def get_non_leaf_nodes(self,roots=[]):
        """
        Returns the names of the root (non-leaves) nodes 

        sage: Tree.to_tree(None).get_non_leaf_nodes()
        []

        sage: Tree.to_tree({'root':'A','children':[ \
        {'root':'B','children':[None,None]}, \
        {'root':'C','children':[ None, \ 
        {'root':'G','children':[None,None]}]}]}).get_non_leaf_nodes()
        ['A', 'B', 'C', 'G']

        sage: Tree.to_tree({'root': 'xor', 'children': [ \
        {'root': 'a', 'children': [x*x]}, \
        {'root': 'b', 'children': [x+1]}]}).get_non_leaf_nodes()
        ['xor', 'a', 'b']

        sage: Tree(Node('a',nchildren=1),children=[ \ 
        Tree(Node('x',nchildren=2), \
        children=[Tree(Node('c',nchildren=1), \
        children=[Tree(Node('leaf',nchildren=0),children=[])]), \
        Tree(Node('d',nchildren=1), \
        children=[Tree(Node('leaf',nchildren=0),\ 
        children=[])])])]).get_non_leaf_nodes()
        ['a', 'x', 'c', 'd']

        sage: Tree(Node('a',nchildren=1), children=[ \
        Tree(Node('d',nchildren=2),children=[Tree(Node('c',nchildren=1), \
        children=[Tree(Node('leaf',nchildren=0),children=[])]), \
        Tree(Node('d',nchildren=1),children=[Tree(Node(x,nchildren=0),\ 
        children=[])])])]).get_non_leaf_nodes()
        ['a', 'd', 'c', 'd']
        """

        if self.is_leaf():
            return roots
        else:
            roots_ = [c.get_non_leaf_nodes(roots) for c in self.children]
            roots = [self.root.name] + flatten(roots_)
            return roots
    
    def get_leaves(self):
        """

        EXAMPLES:

        sage: Tree.leaf_tree().get_leaves()
        [(None, None, [])]

        sage: rs = Tree(Node('A',nchildren=2), children= [ \
        Tree(Node('C',nchildren=1),children=[Tree.leaf_tree()]), \
        Tree(Node('D',nchildren=1),children=[Tree.leaf_tree()])]).get_leaves()
        
        sage: [(str(p),idx,tid) for p,idx,tid in rs]
        [('C[leaf]', 0, ['A', 0, 'C', 0]), ('D[leaf]', 0, ['A', 1, 'D', 0])]
        
        """

        def _get_leaves(t,p,idx,tid):

            assert isinstance(t,Tree)

            if t.is_leaf():  #leaf
                return [(p,idx,tid)]
            else:
                results = [_get_leaves(child, t, idx_, tid + [t.root.name, idx_]) 
                           for idx_, child in Miscs.senumerate(t.children)]

                results = flatten(results,list)
                return results


        return _get_leaves(self,p=None,idx=None,tid=[])





    def gen_trees(self, nodes, vss=None, data={}, blacklist={}):
        """
        Generates trees from nodes whose root is self.root

        blacklist {a: L} disallows a[b[..]] and a[[c..]] 
        where {b,c} in L and only allows 
        [a[x[..]]] where x is not in L

        so for example if we want to force a to be a Leaf then {a:L} 
        where L is all variables (except None). 
        This allows the removal of an extra whitelist

        also if we have {a: L} where L is all variablles (except a) then basically
        we disallow the tree with root 'a' since this says 'a' cannot have 
        any children (including) leaf. 


        EXAMPLES
        sage: map(str,Tree(root=Node('a',nchildren=2), \
        children=[]).gen_trees([Node('b',nchildren=2)]))
        ['a[b[leaf][leaf]][b[leaf][leaf]]', 
        'a[b[leaf][leaf]][leaf]', 
        'a[leaf][b[leaf][leaf]]', 
        'a[leaf][leaf]']
        """

        assert isinstance(nodes,list) and \
            CM.vall(nodes, lambda x: isinstance(x,Node))
        assert vss is None or \
            (isinstance(vss,list) and CM.vall(vss, lambda v: isinstance(v,tuple)))
        assert isinstance(data,dict)
        assert isinstance(blacklist,dict)
 
        if vss is not None:
            children_vss = Miscs.reach(vss, data[self.root.name])
            if children_vss is None:
                return []
        else:
            children_vss = [None] * self.root.nchildren 


        if nodes:
            
            children = nodes + [Node.leaf_node()]
            
            children = [c for c in children \
                            if self.root.name not in blacklist or \
                            c not in blacklist[self.root.name]]
                        
            
            #recursive call
            _gt = lambda r_, nodes_, vss_, : [Tree.leaf_tree()] \
                if r_.is_leaf() else \
                Tree(root=r_,children=[]).gen_trees(nodes    = nodes_,
                                                    vss      = vss_,
                                                    data     = data,
                                                    blacklist= blacklist)
        
            children = [[_gt(c, CM.vsetdiff(nodes,[c]), vs) 
                         for c in children]
                        for vs in children_vss]

            children = [flatten(c) for c in children]

            if len(children) != self.root.nchildren:
                print 'root', root
                print 'vss',vss

                print 'nchildren', nchildren
                print 'len(children)',len(children)
                print 'data', self.root.data
                assert False

            combs = CartesianProduct(*children)
            rs = [Tree(root=self.root,children=c) for c in combs]

        else:
            rs = [Tree(root=self.root, children=[Tree.leaf_tree()] * self.root.nchildren)]


        return rs


    def gen_formula(self, v, data):
        """
        Generate a formula recursively to represent the data structure of tree based on 
        input value v and data.
        

        sage: var('_B_0_C_0__i0 _B_0_C_0__i1')
        (_B_0_C_0__i0, _B_0_C_0__i1)
        
        sage: data1 = {'A': {81: [(2,)], 74: [(1,)], 71: [(0,)]}, \
        'C': {0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], \
        8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]}, \
        'B': {81: [(17,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}}

        sage: Tree(Node('B',nchildren=1), \
        children=[Tree(Node('C',nchildren=1), \
        children=[Tree(Node(_B_0_C_0__i0 + \
        2*_B_0_C_0__i1,nchildren=0),children=[])])]).gen_formula(81, data1)
        _B_0_C_0__i0 + _B_0_C_0__i1*2 == 7

        sage: data2 = {'A': {81: [(2,)], 74: [(1,)], 71: [(0,)]}, \
        'C': {0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], \
        8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]}, \
        'B': {81: [(17,), (9,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}}
        
        sage: Tree(Node('B',nchildren=1), \
        children=[Tree(Node('C',nchildren=1), \
        children=[Tree(Node(_B_0_C_0__i0 + \
        2*_B_0_C_0__i1,nchildren=0),children=[])])]).gen_formula(81, data2)
        Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 7,
        Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 1,
        _B_0_C_0__i0 + _B_0_C_0__i1*2 == 8))      

        #sage: NestedArray.gen_formula(17,{'root':'add','children':[{'root':'C' , 'children':[{'root':'_add_0_C_','children':[100,200]}]},{'root':'D','children':[{'root':'_add_1_D_','children':[100,200]}]}]}, {'C':{0:[(0,)],17:[(1,)],8:[(2,)],3:[(3,),(4,)]},'D':{1:[(0,)],9:[(1,),(3,)],0:[(2,)]},'add':{17:[(8,9),(17,0)],8:[(8,0)],12:[(3,9),(0,12)],3:[(3,0)],'A':{17:[(0,0)],8:[(0,1),(2,1)],12:[(1,0)],3:[(1,1),(2,0)]}}})
        
        """

        if isinstance(self.root.name, CM.sage_expr):
            return self.root.name == v
        
        elif isinstance(self.root.name, dict) and 'first_idx' in self.root.name: 
            #special case {'first_idx':i,'coef':z}
            if v == 0:
                t0 = self.root.name['coef'] == 0
                t1 = self.root.name['first_idx'] == 1
                return Miscs._f([t0,t1],'and',is_real=False)
            else:
                return self.root.name['coef'] == v
        else:
            try:
                idxs = data[self.root.name][v]
            except KeyError: #not reachable, no rel
                return None

            orRs = []
            for idx in idxs:
                andRs = []
                for v_,a_ in zip(idx,self.children):
                    p_ = a_.gen_formula(v_,data)

                    if p_ is None:
                        andRs = None
                        break
                    andRs.append(p_)


                if andRs is not None:
                    assert len(andRs)>0
                    andRs = Miscs._f(andRs,'and',is_real=False) 
                    orRs.append(andRs)

            orRs = Miscs._f(orRs,'or',is_real=False)
            return orRs
        
    


    ##### Static Methods for Tree #####
    @staticmethod
    def from_tree(t):
        """
        Generate a dictionary  from a tree

        """
        if t.is_leaf():
            return None
        else:
            return {'root':t.root.name, 
                    'children':map(Tree.from_tree,t.children)}
                    

    @staticmethod
    def to_tree(d):
        """
        Generate a tree using a dictionary 
        
        sage: print Tree.to_tree({'root':'add','children':[{'root':'C' , 'children':[None]},{'root':'D','children':[None]}]})
        add[C[leaf]][D[leaf]]
        sage: print Tree.to_tree({'root':'add','children':[{'root':'C' , 'children':[None]},{'root':'D','children':[None]}]}).__str__(print_structure=True)
        Tree(root=Node(name='add', nchildren=2, is_ordered=True),children=[Tree(root=Node(name='C', nchildren=1, is_ordered=True),children=[Tree(root=Node(name='leaf', nchildren=0, is_ordered=False),children=[])]),Tree(root=Node(name='D', nchildren=1, is_ordered=True),children=[Tree(root=Node(name='leaf', nchildren=0, is_ordered=False),children=[])])])
        """
        if d is None:
            return Tree.leaf_tree()
        elif isinstance(d,dict) and 'root' in d and 'children' in d:
            return Tree(Node(d['root'],nchildren=len(d['children'])), \
                            children=map(Tree.to_tree,d['children']))
        else:
            return Tree(Node(d),children=[])


    @staticmethod
    def leaf_tree(): 
        return Tree(root=Node.leaf_node(),children=[])
    

 
class AEXP(object):

    def __init__(self,lt,rt):
        """
        Initialize AEXP (Array Expression) which has the form left_tree = right_tree,
        e.g.  A[leaf][leaf] = B[C[leaf][leaf]][D[leaf]]

        """
        assert isinstance(lt,Tree)
        assert isinstance(rt,Tree)

        self.lt = lt
        self.rt = rt

    def __str__(self,leaf_content=None,do_lambda_format=False,print_structure=False):
        """
        Returns the str of AEXP

        leaf_content: {},None,str
        Instantiates leaves of rt with leaf_content, e.g. A[x], leaf_info={x:5} => A[5]
        
        do_lambda_format: T/F
        Returns a lambda format of array expressions for evaluation

        EXAMPLES:

        sage: AEXP(Tree(Node('v',1),[Tree.leaf_tree()]),Tree(Node('a',1),
        children=[Tree(Node('x3',3),[Tree.leaf_tree(),Tree.leaf_tree(),
        Tree.leaf_tree()])])).__str__()
        'v[i1] == a[x3[(i1)_][(i1)_][(i1)_]]'

        sage: AEXP(Tree(Node('v',1),[Tree.leaf_tree()]),
        Tree(Node('a',1),children=[Tree(Node('x3',3),
        [Tree.leaf_tree(),Tree.leaf_tree(),
        Tree.leaf_tree()])])).__str__(do_lambda_format=True)
        'lambda v,a,x3,i1: v[i1] == a[x3[(i1)_][(i1)_][(i1)_]]'

        sage: AEXP(Tree(Node('v',1),[Tree.leaf_tree()]),
        Tree(Node('a',1),children=[Tree(Node('x3',3),[Tree.leaf_tree(),
        Tree(Node('c',2),[Tree.leaf_tree(),Tree.leaf_tree()]),
        Tree.leaf_tree()])])).__str__(do_lambda_format=True)
        'lambda v,a,x3,c,i1: v[i1] == a[x3[(i1)_][c[(i1)_][(i1)_]][(i1)_]]'

        sage: AEXP(Tree(Node('v',1),[Tree.leaf_tree()]),
        Tree(Node('a',1),children=[Tree(Node('x3',3),
        [Tree.leaf_tree(),Tree(Node('c',2),[Tree.leaf_tree(),Tree.leaf_tree()]),
        Tree(Node(x+7,0),[])])])).__str__(leaf_content={x:5},do_lambda_format=True)
        'lambda v,a,x3,c,i1: v[i1] == a[x3[leaf][c[leaf][leaf]][12]]'
        
        sage: var('y')
        y
        sage: AEXP(Tree(Node('v',1),[Tree.leaf_tree()]),Tree(Node('a',1),
        children=[Tree(Node('x3',3),[Tree.leaf_tree(),Tree(Node('c',2),
        [Tree.leaf_tree(),Tree(Node(x-y,0),[])]),
        Tree(Node(x+7,0),[])])])).__str__(leaf_content={x:5,y:7},do_lambda_format=False)
        'v[i1] == a[x3[leaf][c[leaf][-2]][12]]'
        """

        if print_structure:
            lt = self.lt.__str__(leaf_content=None, print_structure=True)
            rt = self.rt.__str__(leaf_content=None, print_structure=True)
            return 'AEXP(lt=%s,rt=%s)'%(lt, rt)


        l_idxs, l_iformat, l_aformat = self.lt.get_str_formats()

        if leaf_content is None:
            r_idxs = "(%s)_"%l_aformat
            rt = self.rt.__str__(leaf_content=r_idxs)
        else:
            assert isinstance(leaf_content,dict)
            rt = self.rt.__str__(leaf_content=leaf_content)

        
        rs = '%s%s == %s'%(self.lt.root,l_iformat,rt)

        if do_lambda_format:
            l_idxs_ = ','.join(['i%s'%li for li in l_idxs])
            nodes = [self.lt.root.name]  + CM.vset(self.rt.get_non_leaf_nodes())
            lambda_ = 'lambda %s,%s' %(','.join(nodes),l_aformat)
            rs= '%s: %s'%(lambda_,rs)
        
        return rs

    @staticmethod
    def gen_nestings(nodes,vss,data,blacklist,verbose):
        """
        Generates nestings from a set of nodes. E.g., given nodes [a,b,c], 
        returns all nestings, e.g. [{a,[b,c],{a,[c,b]}},{b,[a,c]} ..
        Also performs some prelim pruning based on trace data

        EXAMPLES:

        #todo: check me
        #sage: res = Miscs.gen_trees(['a','b','c'],{'a':1,'b':2,'c':3},{});len(res)
        477

        """

        assert isinstance(nodes,list) and \
            CM.vall(nodes, lambda x: isinstance(x, Node))
        assert vss is None or \
            (isinstance(vss,list) and CM.vall(vss, lambda v: isinstance(v,tuple)))
        assert isinstance(data,dict)
        assert isinstance(blacklist, dict)
        

        def _gt(root):
            t = Tree(root=root, children=[])
            ts = t.gen_trees(nodes     = CM.vsetdiff(nodes,[root]), 
                             vss       = vss, 
                             data      = data,
                             blacklist = blacklist)
            return ts
        

        trees = [ _gt(node) for node in nodes]
        trees = flatten(trees)

        assert CM.vall(trees, lambda t: isinstance(t,Tree))

        return trees
    
    @staticmethod
    def gen_aexps(nodes, data, xinfo, verbose):
        """
        arrs = [a,b,c]
        returns a=allpostrees(b,c)  , b = allpostrees(a,b)  , etc

        sage: map(str,AEXP.gen_aexps([Node('A',1),Node('C',1),Node('B',1)],
        data={'A': {1: [(1,)], -3: [(2,)], 7: [(0,)]}, 
        'C': {1: [(5,)], 2: [(4,)], 4: [(6,)], 5: [(1,)], 6: [(2,), (3,)], 8: [(0,)]}, 
        'B': {0: [(4,)], 1: [(0,), (3,), (6,)], 7: [(5,)], -3: [(1,)], 5: [(2,)]}}, 
        xinfo={'All': ['A', 'B', 'C'], 'Const': [], 'Assume': [], 
        'Global': [], 'ZDims': {'A': 1, 'C': 1, 'B': 1}, 'Expect': [], 
        'ExtFun': [], 'Input': [], 'Output': []},verbose=1))
        * gen_aexps [A,C,B]: 2 expressions generated
        ['A[i1] == B[C[(i1)_]]', 'A[i1] == B[(i1)_]']

        sage: map(str,AEXP.gen_aexps([Node('A',1),Node('C',1),Node('B',1)],
        data={}, xinfo={'All': ['A', 'B', 'C'], 'Const': [], 
        'Assume': [], 'Global': [], 'ZDims': {'A': 1, 'C': 1, 'B': 1}, 
        'Expect': [], 'ExtFun': [], 'Input': [], 'Output': []},verbose=1))
        * gen_aexps [A,C,B]: 12 expressions generated
        ['A[i1] == C[B[(i1)_]]', 'A[i1] == C[(i1)_]', 'A[i1] == B[C[(i1)_]]', 
        'A[i1] == B[(i1)_]', 'C[i1] == A[B[(i1)_]]', 'C[i1] == A[(i1)_]', 
        'C[i1] == B[A[(i1)_]]', 'C[i1] == B[(i1)_]', 'B[i1] == A[C[(i1)_]]', 
        'B[i1] == A[(i1)_]', 'B[i1] == C[A[(i1)_]]', 'B[i1] == C[(i1)_]']
        """
        
        assert isinstance(nodes, list) and CM.vall(nodes, lambda x: isinstance(x, Node))
        assert isinstance(xinfo, dict)
        assert isinstance(data, dict)

        blacklist = AEXP.gen_blacklist(xinfo, verbose=verbose)


        #Generate nestings
        def _gt(nodes, ln, data):
            try:
                vss = data[ln.name].keys()
                assert CM.vall(vss, lambda v: not CM.is_iterable(v))
                vss=map(lambda v: tuple([v]),vss)
            except KeyError:
                vss = None
                
            rs =  AEXP.gen_nestings(nodes=nodes,vss=vss, data=data, 
                                    blacklist=blacklist,verbose=verbose)
                                    
                                    
            return rs

        #Construct an AEXP
        _ga = lambda x: Tree(x, children=[Tree.leaf_tree()] * x.nchildren)

        if xinfo['Output']:
            #x = a[b[...]], x in output vars and a,b not in output vars
            anodes, lnodes = \
                CM.vpartition(nodes, lambda x: x.name in xinfo['Output'])

            aexps = [[AEXP(_ga(ln),rn) for rn in _gt(anodes,ln,data)]
                     for ln in lnodes]

        else:
            aexps= [[AEXP(_ga(ln),rn) for rn in _gt(CM.vsetdiff(nodes,[ln]),ln,data)]
                    for ln in nodes]
        
        aexps = flatten(aexps)

        #filter out unlikely array expressions
        aexps = [ae for ae in aexps if ae.is_ok(xinfo)]

        if verbose >= 1:
            print '* gen_aexps [%s]: %d expressions generated'\
                %(','.join(map(str,nodes)),len(aexps))

            if verbose >= 2:
                arrStrs = ['%d. %s'%(i,ae) for i,ae in Miscs.senumerate(aexps)]
                print '\n'.join(arrStrs)

        return aexps

    def gen_template(self,idxs_vals=None,special=False,verbose=1):
        """
        special = True then it means we only have 1 data to compare against
        thus if the pass in indices of the leaves are 0's  , the result will be  z + 0*i = 0 
        which then just gives z = 0, doesn't contribute to anything if we have only 1 data.
        Thus special flag turns the result z + 0*i = 0 into z = 0 and i = 1.

        EXAMPLES:

        sage: NestedArray.genTemplate(({'root':'R','children':[None,None,None]},{'root': 'add', 'children': [{'root': 'C', 'children': [None]}, {'root': 'D', 'children': [None]}]}),verbose=1)
        ({'root': 'R', 'children': [None, None, None]}, {'root': 'add', 'children': [{'root': 'C', 'children': [_add_0_C_0__i1*i1 + _add_0_C_0__i2*i2 + _add_0_C_0__i3*i3 + _add_0_C_0__i0]}, {'root': 'D', 'children': [_add_1_D_0__i1*i1 + _add_1_D_0__i2*i2 + _add_1_D_0__i3*i3 + _add_1_D_0__i0]}]})


        sage: NestedArray.genTemplate(({'root':'R','children':[None,None]},{'root': 'add', 'children': [{'root': 'C', 'children': [None]}, {'root': 'D', 'children': [None]}]}),verbose=1)
        ({'root': 'R', 'children': [None, None]}, {'root': 'add', 'children': [{'root': 'C', 'children': [_add_0_C_0__i1*i1 + _add_0_C_0__i2*i2 + _add_0_C_0__i0]}, {'root': 'D', 'children': [_add_1_D_0__i1*i1 + _add_1_D_0__i2*i2 + _add_1_D_0__i0]}]})

        sage: NestedArray.genTemplate(({'root':'R','children':[None,None]},{'root': 'add', 'children': [None,None]}),idxs_vals=[0,0],special=True)
        ({'root': 'R', 'children': [None, None]}, {'root': 'add', 'children': [{'coef': _add_0__i0, 'first_idx': _add_0__i1}, {'coef': _add_1__i0, 'first_idx': _add_1__i1}]})

        sage: NestedArray.genTemplate(({'root':'R','children':[None,None]},{'root': 'add', 'children': [None,None]}),idxs_vals=[0,0],special=False)
        ({'root': 'R', 'children': [None, None]}, {'root': 'add', 'children': [_add_0__i0, _add_1__i0]})

        """
        #special implies idxs=(0,..,0)
        assert not special or CM.vall(idxs_vals,lambda x: x==0)

        #idxs_vals is None implies special=False
        assert idxs_vals is not None or not special

        rt = deepcopy(self.rt)  #make a copy

        leaves = rt.get_leaves()
        leaves = [(p,idx,tid) for p,idx,tid in leaves if p is not None]

        #print 'gh'
        #print [(str(p),idx,tid) for p,idx,tid in leaves if p is not None]        

        if idxs_vals is None:
            ts = [1]+[var('i%d'%(i+1)) for i in srange(self.lt.root.nchildren)]
        else:
            ts = [1]+ list(idxs_vals)
        
        for p,idx,tid in leaves:
            prefix = '_%s__i'%'_'.join(map(str,tid))
            if special:
                rs = {'first_idx':var(prefix+str(1)),'coef':var(prefix+str(0))}
            else:
                rs = Miscs.gen_template(ts,rv=None,prefix=prefix,verbose=verbose)
        
            p.children[idx]= Tree(Node(name=rs,nchildren=0,is_ordered=True),children=[])
            assert isinstance(p,Tree)


        return AEXP(lt=self.lt,rt=rt)


    def is_ok(self, xinfo):
        """
        Return True if this nesting is fine. Otherwise, returns False, which marks
        the nesting for pruning.

        e.g., Those that do not contain the input variables
        """
        

        #all inputs must be in rt
        roots = self.rt.get_non_leaf_nodes()
        inputVars = xinfo['Input']
        rs = CM.vall(inputVars, lambda iv: iv in roots)
        
        return rs

    def peelme(self, data, verbose):
        """
        Go through each nesting (aexp), generate a SMT formula, and checks its satisfiability.


        EXAMPLES:


        sage: AEXP(lt=Tree(root=Node(name='A', nchildren=1, is_ordered=True),\
        children=[Tree(root=Node(name='leaf', nchildren=0,is_ordered=False),children=[])]),\
        rt=Tree(root=Node(name='B', nchildren=1, is_ordered=True),\
        children=[Tree(root=Node(name='C', nchildren=1, is_ordered=True),\
        children=[Tree(root=Node(name='leaf', nchildren=0, is_ordered=False),\
        children=[])])])).peelme(data={'A': {1: [(1,)], -3: [(2,)], \
        7: [(0,)]}, 'C': {1: [(5,)], 2: [(4,)], 4: [(6,)], 5: [(1,)], \
        6: [(2,), (3,)], 8: [(0,)]}, 'B': {0: [(4,)], \
        1: [(0,), (3,), (6,)], 7: [(5,)], -3: [(1,)], 5: [(2,)]}},verbose=1)
        ['lambda A,B,C,i1: A[i1] == B[C[2*i1 + 1]]']

        sage: AEXP(lt=Tree(root=Node(name='A', nchildren=1, is_ordered=True),\
        children=[Tree(root=Node(name='leaf', nchildren=0,is_ordered=False),children=[])]),\
        rt=Tree(root=Node(name='B', nchildren=1, is_ordered=True),\
        children=[Tree(root=Node(name='C', nchildren=1, is_ordered=True),\
        children=[Tree(root=Node(name='leaf', nchildren=0, is_ordered=False),\
        children=[])])])).peelme(data={'A': { \
        7: [(0,)]}, 'C': {1: [(5,)], 2: [(4,)], 4: [(6,)], 5: [(1,)], \
        6: [(2,), (3,)], 8: [(0,)]}, 'B': {0: [(4,)], \
        1: [(0,), (3,), (6,)], 7: [(5,)], -3: [(1,)], 5: [(2,)]}},verbose=2)
        ['lambda A,B,C,i1: A[i1] == B[C[_B_0_C_0__i1*i1 + 1]]']


        sage: rs = (AEXP(lt=Tree.to_tree({'root':'A','children':[None]}), \ 
        rt=Tree.to_tree({'root':'B',\ 
        'children':[{'root':'C','children':[None]}]})).peelme( \
        {'A':{71:[(0,)],74:[(1,)],81:[(2,)]},\ 
        'B':{71:[(5,),(7,)],74:[(6,),(8,)],81:[(17,)]},\ 
        'C':{0:[(0,),(3,)],9:[(1,),(8,)],7:[(2,),(5,)],\ 
        1:[(4,)],8:[(6,)],17:[(7,)]}},verbose=1))
        sage: print '\n'.join(rs)
        lambda A,B,C,i1: A[i1] == B[C[i1 + 5]]


        sage: rs = AEXP(lt=Tree.to_tree({'root':'A','children':[None]}),rt=Tree.to_tree({'root':'add','children':[{'root':'C' , 'children':[None]},{'root':'D','children':[None]}]})).peelme(data = {'C':{0:[(0,)],17:[(1,)],8:[(2,)],3:[(3,),(4,)]},'D':{1:[(0,)],9:[(1,),(3,)],0:[(2,)]},'add':{17:[(8,9),(17,0)],8:[(8,0)],12:[(3,9),(0,12)],3:[(3,0)]},'A':{17:[(0,0)],8:[(0,1)],12:[(1,0)],3:[(1,1)]}},verbose=1)
        sage: print '\n'.join(rs)
        lambda A,add,C,D,i1: A[i1] == add[C[i1 + 2]][D[1]]
        lambda A,add,C,D,i1: A[i1] == add[C[i1 + 2]][D[3]]
        lambda A,add,C,D,i1: A[i1] == add[C[2*i1 + 2]][D[3]]
        lambda A,add,C,D,i1: A[i1] == add[C[2*i1 + 2]][D[1]]
        """

        _gen_template = lambda iv,sp: \
            self.gen_template(idxs_vals=iv,special=sp,verbose=verbose)
                                    

        vi = [[(v,ids) for ids in idxs] for v,idxs in data[self.lt.root.name].items()]
        vi = flatten(vi,list)

        if verbose >= 2:
            print 'vi: ', vi

        sts = [_gen_template(ids,sp=len(vi)==1).rt for _,ids in vi]

        formula = [rh.gen_formula(v,data) for (v,_),rh in zip(vi,sts)]
        formula = Miscs._f(formula,'and',is_real=False)
        if formula is None:
            return None

        import z3
        from smt_z3py import SMT_Z3

        s = z3.Solver()
        s.add(formula)


        ms = SMT_Z3.get_models(s,k=10)
        if len(ms) == 0: #no model, formula is unsat, i.e. no relation
            return None

        ds = [SMT_Z3.get_constraints(m,result_as_dict=True) for m in ms]
              
        #generate the full expression
        template = _gen_template(None,False)

        rs = [template.__str__(leaf_content=d,do_lambda_format=True) for d in ds]
        assert CM.vall(rs, lambda x: isinstance(x,str))

        return rs


    ##### Static method for AEXPS #####

    @staticmethod
    def gen_blacklist(xinfo,verbose=1):
        """
        Takes advantage of user inputs to reduce the number of generated nestings

        EXAMPLES:

        sage: Tree.gen_blacklist({'All':['R','A','B','D','E','xor','g'],
        'Input':['A','B'],'Output':['R'],'Global':[],'Const':[],
        'ExtFun':['xor'],'Global':['g']})
        {'A': ['R', 'A', 'B', 'D', 'E', 'xor', 'g'], 
        'R': ['R', 'A', 'B', 'D', 'E', 'xor', 'g', None], 
        'B': ['R', 'A', 'B', 'D', 'E', 'xor', 'g'], 'xor': [None], 'g': [None]}
        
        """

        allVars    = xinfo['All']
        inputVars  = xinfo['Input']
        outputVars = xinfo['Output']
        globalVars = xinfo['Global']
        constVars  = xinfo['Const']
        extFuns    = [x for x in xinfo['ExtFun']]

        #Inputs must be leaves
        #e.g., a[i] = x[y[i']] is not possible
        #e.g., a[i] = xor[x[i'][y[i']]
        inputsLeaves = [{inp:allVars} for inp in inputVars]

        #Const must be leaves
        constLeaves = [{c:allVars} for c in constVars]

        #Extfuns are never leaves
        #e.g.,  r[i] = a[b[xor[i'][i']]]  is not possible
        extfunsNotLeaves = [{ef:[None]} for ef in extFuns]

        #Globals are never leaves
        globalsNotLeaves = [{gv:[None]} for gv in globalVars]

        #Outputs should never be part of the tree
        outputsNotInTree = [{oup:allVars + [None]} for oup in outputVars]

        ds = inputsLeaves+constLeaves + extfunsNotLeaves + \
            globalsNotLeaves + outputsNotInTree
        rs = CM.merge_dict(ds)
        return rs


    def solve1(self): #nested arrays
        
        print "Generate array expressions (nestings)"
        aexps = AEXP.gen_aexps(nodes   = self.nodes,
                               data    = self.tcs1[0],
                               xinfo   = self.xinfo,
                               verbose = self.verbose)
        
        print '* Find valid nestings using reachability analysis'
        smtResults = []
        for i,ae in Miscs.senumerate(aexps):
            sRes = ae.peelme(self.tcs1[0], verbose=self.verbose)
            if sRes is not None:

                smtResults = smtResults + sRes

                if self.verbose >= 1:
                    print '%d. %s has %d relation(s)'%(i,ae,len(sRes))
                    print '\n'.join(sRes)


        print '* Relations: %d'%(len(smtResults))

        self.set_sols(smtResults)



    @staticmethod
    def createExtFun(fn,avals,doDict=False,verbose=1):
                     
        """
        if function is not commutative then will return a complete set (CartesianProd)
        of idxs

        e.g., if avals = [1,2,3], and fn is a 3-ary function
        then will get idxs of f(1,1,1), f(1,2,3), f(1,3,2), f(2,2,2)
        if do_caretesian=False then will return only the Permutation.
        In other words,  doCartesianProd makes the results much larger !

        Note: did not use caching because caching makes it slower.
        Probably because these functions are too simple that 
        doesn't worth the caching overhead  

        EXAMPLES:



        sage: ExtFun.createExtFun('xor_xor',[[1,7,9,1000]],doDict=False)
        [[1, 7, 9, 1000]]

        sage: ExtFun.createExtFun('xor_xor',[[1,7,9,1000]],doDict=True)
        * fun: xor_xor, fvals 0, idxs 0
        {'xor_xor': {}}

        sage: ExtFun.createExtFun('xor_xor',[[1,7,9,1000]],doDict=True)
        * fun: xor_xor, fvals 0, idxs 0
        {'xor_xor': {}}
        

        sage: ExtFun.createExtFun('sub',[[1,2],[5,6]], doDict=False,verbose=1)
        [0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6]

        sage: ExtFun.createExtFun('sub',[[1,2],[5,6]],doDict=True,verbose=1)
        * fun: sub, fvals 9, idxs 16
        {'sub': {0: [(1, 1), (2, 2), (5, 5), (6, 6)], 1: [(2, 1), (6, 5)], 3: [(5, 2)], 4: [(5, 1), (6, 2)], 5: [(6, 1)], -5: [(1, 6)], -4: [(1, 5), (2, 6)], -3: [(2, 5)], -1: [(1, 2), (5, 6)]}}

        sage: ExtFun.createExtFun('add',[[1,2,3,4],[5,6],[7,8,9]], doDict=False)
        [[1, 2, 3, 4], [5, 6], [7, 8, 9], [6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]

        sage: ExtFun.createExtFun('add',[[1,2,3,4],[5,6],[7,8,9]], doDict=True)
        * fun: add, fvals 10, idxs 26
        {'add': {6: [(1, 5)], 7: [(1, 6), (2, 5)], 8: [(2, 6), (3, 5), (1, 7)], 9: [(3, 6), (4, 5), (1, 8), (2, 7)], 10: [(4, 6), (1, 9), (2, 8), (3, 7)], 11: [(2, 9), (3, 8), (4, 7)], 12: [(3, 9), (4, 8), (5, 7)], 13: [(4, 9), (5, 8), (6, 7)], 14: [(5, 9), (6, 8)], 15: [(6, 9)]}}

        """        
        fun = ExtFun.get_fun(fn)
        is_commute = ExtFun.is_commute(fn)

        from inspect import getargspec
        funNArgs = len(getargspec(fun)[0])

        if is_commute:
            avals_ = [flatten(av) for av in avals]
            combs = Combinations(avals_,funNArgs)  #"[A,B,C],2 -> [A,B], [A,C], [B,C]"
            cps = [tuple(CartesianProduct(*c)) for c in combs]
            idxs = flatten(cps,ltypes=tuple)
            idxs = CM.vset(idxs,idfun=repr)
            idxs = CM.vset(idxs, Set) #[(1, 2), (2, 1),(2,2)] => [(1, 2), (2, 2)]

        else:
            avals = CM.vset(flatten(avals))
            alists = [avals]*funNArgs
            idxs = CartesianProduct(*alists)


        fun_vals = [fun(*idx) for idx in idxs]
        if not doDict: #returns fun_vals as well as the orig avals
            if is_commute:
                res = avals
                if fun_vals:  # != [] zen
                    res = avals + [CM.vset(fun_vals)]
            else:
                res =  CM.vset(fun_vals + avals)

        else:  #create dict
            cs = zip(fun_vals,idxs)
            cs = [(fv,tuple(idx)) for (fv,idx) in cs]

            d_contents = CM.create_dict(cs)
            res = {fn:d_contents}

            if verbose >= 1:
                print '* fun: %s, fvals %d, idxs %d'\
                    %(fn,len(d_contents.keys()),
                      len(idxs) if isinstance(idxs,list)\
                        else idxs.cardinality())
        return res



    
    def replace_leaf(self,tid, special,ts,verbose):
        """
        EXAMPLES:
        sage: rs = Tree({'root':'A','children': [ \
        {'root':'C','children':[None,None]}, \
        {'root':'D','children':[None]}]})
        sage: rs.replace_leaf(tid=[],special=True,ts=None,verbose=1)
        sage: print rs
        A[C[{'coef': _0_0__i0, 'first_idx': _0_0__i1}]
        [{'coef': _0_1__i0, 'first_idx': _0_1__i1}]]
        [D[{'coef': _1_0__i0, 'first_idx': _1_0__i1}]]


        sage: var('y')
        y
        sage: rs = Tree({'root':'A','children': [ \
        {'root':'C','children':[None,None]}, \
        {'root':'D','children':[None]}]})
        sage: rs.replace_leaf(tid=[],special=False,ts=[1,x,y],verbose=1)
        sage: print rs
        A[C[_A_0_C_0__i1*x + _A_0_C_0__i2*y + _A_0_C_0__i0]
        [_A_0_C_1__i1*x + _A_0_C_1__i2*y + _A_0_C_1__i0]]
        [D[_A_1_D_0__i1*x + _A_1_D_0__i2*y + _A_1_D_0__i0]]

        todo:
        there's a BUG here (hence it's not being used):  
        the reason is replacement is no longer a valid tree !
        
        """
        assert isinstance(tid,list)

        if self.is_leaf():
            prefix = '_%s__i'%'_'.join(map(str,tid))
            if special:
                root = {'first_idx':var(prefix+str(1)),'coef':var(prefix+str(0))}
            else:
                root = Miscs.gen_template(ts,rv=None,prefix=prefix,verbose=verbose)
            
            self.root = root

        else:
            assert isinstance(self.get_children(),list)
            for i,c in Miscs.senumerate(self.children):
                c.replace_leaf(tid + [self.get_root(), i],special,ts,verbose)
