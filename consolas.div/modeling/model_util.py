from z3 import *

import itertools

downcasefirst = lambda s: s[:1].lower() + s[1:] if s else ''
_Or = lambda x: next(iter(x)) if len(x)==1 else Or(x)
_And = lambda x: next(iter(x)) if len(x)==1 else And(x)
_A_STRANGE_INT = 47731477

class ClassNotDefined:
    def __init__(self, name):
        self.name = name
        
    def __repr__(self):
        return "<%s>" % self.name

class DataType:
    INT = 1
    BOOL = 2

class ClassDiagram:
    def __init__(self, name):
        self.name = name;
        self.classes = set()
        self.superclass = dict()
        self.ref = dict()
        self.multiref = dict()
        self.manref = set()
        self.attr = dict()
        
        
    def define_class(self, class_name, supper_class = []):
        if supper_class == None or len(supper_class)==0:
            self.classes.add(class_name)
        else:
            if any(not(x in self.classes) for x in supper_class):
                raise ClassNotDefined("One of the supper classes of %s" % class_name)
            self.classes.add(class_name)
            self.superclass[class_name] = supper_class
            
    def define_ref(self, name, fromclass, toclass, mandatory=False):
        if not (fromclass in self.classes) :
            raise ClassNotDefined(fromclass)
        if not (toclass in self.classes) :
            raise ClassNotDefined(toclass)
        self.ref[name] = (fromclass, toclass)
        if mandatory: 
            self.manref.add(name)
        
    def define_attr_int(self, name, cls, min = 0, max = 1):
        self.attr[name] = (cls, min, max)
        
    def define_attr_bool(self, name, cls):
        self.attr[name] = (cls, True)    
        
class ModelSMT:
    def __init__(self, class_diagram):
        self.cd = class_diagram
        self.maxinst = dict()  # max number of instances for each type
        self.inst_by_type = dict()
        
        self.nullinst = None
        self.typeof = None
        self.alive = None
        
        self.CompType = None
        self.CompInst = None
        
        self.types = dict()
        self.insts = dict()
        self.funcs = dict()
        self.indirect_super_class = None
        self.indirect_insts = None
        self.leaf_classes = None
        self.children_leaf_classes = None
        self.declared_type = None
        
        self.hard_const = []
        
        self.const_count = 1000
    
    def hard(self, const, comment):
        self.hard_const.append( (const, comment) )
        
    def generate(self):
        
        class_names = list(self.cd.classes)
        self.leaf_classes = set([x for x in class_names if not(any(y for y in class_names if x in self.cd.superclass.get(y,[])))])
        
        insupc = dict()
        for cn in class_names:
            insupc[cn] = set(self.cd.superclass.get(cn, []))
        
        for k in class_names:
            for i in class_names:
                for j in class_names:
                    if j in insupc[i]:
                        insupc[i] = insupc[i] | insupc[j]
        self.indirect_super_class = insupc
        
        clsleafch = dict()
        for cn in class_names:
            clsleafch[cn] = set([x for x in self.leaf_classes if cn in set([x])|insupc[x]])
        clsleafch['NullType'] = set(['NullType'])
        self.children_leaf_classes = clsleafch
        
        CompType, comp_types = EnumSort("CompType", ["NullType"]+class_names)
        self.CompType = CompType
        inst_names = []
        declared_type = dict()
        indirect_insts = dict([(c, set()) for c in class_names])
        for cname in class_names:
            inum = self.maxinst.get(cname, 0)
            cname_lower = downcasefirst(cname)
            local_inst_names = ["%s%02d" % (cname_lower, i) for i in range(0, inum) ]
            for i in local_inst_names:
                declared_type[i] = cname
                for c in set([cname]) | insupc[cname]:
                    indirect_insts[c].add(i) 
            inst_names = inst_names + local_inst_names
        self.indirect_insts = indirect_insts
        declared_type['null'] = 'NullType'   
        self.declared_type = declared_type
        inst_names_set = set(inst_names)
            
        CompInst, comp_insts = EnumSort("CompInst", ['null'] + inst_names)
        self.CompInst = CompInst
        nullinst = comp_insts[0]
        NullType = comp_types[0]
        
        for ct in comp_types : self.types[str(ct)] = ct
        for ci in comp_insts : self.insts[str(ci)] = ci
        
        typeof = Function('typeof', CompInst, CompType)
        alive = Function('alive', CompInst, BoolSort())   
        self.typeof = typeof
        self.alive = alive
        
        self.hard(typeof(nullinst) == NullType, "null-type")
        self.hard(Not(alive(nullinst)), "null-not-alive")
        
        #constraints for types
        for instn, inst in self.insts.iteritems():
            if instn == 'null':
                continue
            leaves = clsleafch[declared_type[instn]]
            self.hard( _Or([typeof(inst)==self.types[t] for t in leaves | set(['NullType']) ]),
                       "one-of-the-leaf-types" )
        self.hard(_And([ Not(alive(i)) == (typeof(i)==NullType) for i in self.insts.itervalues()]),
                  "not-alive-no-type")
        
        #declare functions for references
        refs = [Function(fn, CompInst, CompInst) for fn in self.cd.ref.iterkeys()]
        for fun in refs: self.funcs[str(fun)] = fun
        
        #constraints for references
        for funname, (fromclass, toclass) in self.cd.ref.iteritems():
            fun = self.funcs[funname]
            type_overlap = lambda x, y : clsleafch[x] & clsleafch[y]
            from_insts = set([x for x in inst_names if type_overlap(fromclass, declared_type[x])])
            #to_insts = [x for x in inst_names if type_overlap(toclass, declared_type[x])]
            from_leaf_cls = clsleafch[fromclass]
            to_leaf_cls = clsleafch[toclass]
            
            self.hard( 
                      _And([ fun(self.insts[x])==nullinst for x in inst_names_set - from_insts ]),
                      "ref-not-domain" )
            self.hard( _And([
                              _Or([typeof(fun(self.insts[x]))==self.types[y] for y in to_leaf_cls | set(['NullType'])])
                              for x in from_insts
                              ]),
                      "ref-right-codomain" )
            self.hard( _And([
                             Implies(
                                     Not(self.g_istypeof(x, fromclass)),
                                     fun(self.insts[x])==nullinst
                                     )
                             for x in from_insts if not(fromclass in insupc[declared_type[x]])
                             ]), "ref-not-proper-domain")
            if funname in self.cd.manref:
                self.hard( 
                          _And([
                                Implies(
                                        And(alive(self.insts[x]), self.g_istypeof(x, fromclass)), 
                                        alive(fun(self.insts[x]))
                                        ) 
                                for x in from_insts]), 
                          'mandatory_ref'
                          )
            self.hard( _And([Implies(Not(alive(self.insts[x])), fun(self.insts[x])==nullinst) for x in from_insts]), 'mandatory_ref')
    
        #end of for
        
        #declare functions for attributes
        for attr, dec in self.cd.attr.iteritems():
            cls = dec[0]
            relevs = self.get_potential_instances(cls)
            irrelevs = set(self.insts.keys()) - relevs
            if len(dec) == 2: #boolean
                fun = Function(attr, CompInst, BoolSort())
                self.funcs[attr] = fun
                self.hard(
                          _And([Not(fun(self.insts[x])) for x in irrelevs]),
                          "Irrelevant Bool attribute"
                          )
                self.hard(
                          _And([Or(
                                    self.g_istypeof(x, cls),
                                    Not(fun(self.insts[x]))
                                  )
                                for x in relevs
                                ]),
                          "Relevant by not proper type of Bool attribute"
                          )
            if len(dec) == 3: #int
                (cls, min, max)=dec
                fun = Function(attr, CompInst, IntSort())
                self.funcs[attr]=fun
                self.hard(_And([fun(x)==_A_STRANGE_INT
                                for x in [self.insts[inst] for inst in irrelevs]
                                ]
                               ),
                          "Irrelalevant int attributes"
                          )
                item = self.gen_const_inst()    
                self.hard(
                          _And([If(
                                  self.g_istypeof(str(x), cls),
                                  And(fun(x)>=min, fun(x)<=max),
                                  fun(x) == _A_STRANGE_INT
                                  )
                                for x in [self.insts[inst] for inst in relevs]
                                ]
                               ),
                          "Relevant int attributes"
                          )
    def g_istypeof(self, inst, cls):
        declared_type = self.declared_type[str(inst)]
        if cls in set([declared_type]) | self.indirect_super_class[declared_type]:
            return True
        possible = self.children_leaf_classes[self.declared_type[str(inst)]]
        leaf_cls = self.children_leaf_classes[cls]
        return _Or([self.typeof(self.insts[inst])==self.types[y] for y in possible & leaf_cls])        
    
    def g_type_dep(self, fun, fromcls, tocls):
        result = []
        fromleaves = set([])
        for cls in fromcls:
            fromleaves = fromleaves | self.children_leaf_classes[cls]
            
        toleaves = set([])
        for cls in tocls:
            toleaves = toleaves | self.children_leaf_classes[cls]
        
        for inst in self.insts.iterkeys():
            #only if inst is possible to be a instance of one of the from classes
            print inst
            print self.declared_type[inst]
            if self.children_leaf_classes[self.declared_type[inst]] & fromleaves:
                cst = Implies(
                              _Or([self.typeof(self.insts[inst])==self.types[cls] for cls in fromleaves]),
                              _Or([self.typeof(self.funcs[fun](self.insts[inst]))==self.types[cls] for cls in toleaves])
                              )
                result.append(cst)
        return result
    
    def get_potential_instances(self, cls):
        return set([x for x in self.insts 
                if self.children_leaf_classes[self.declared_type[x]] & self.children_leaf_classes[cls]
                ])
    
    def gen_const_inst(self):
        x = Const('inst%05d'%self.const_count, self.CompInst)
        self.const_count += 1
        return x
    
    def g_prpg_multi(self, inst_types, expr):
        pool = [self.get_potential_instances(str(cls)) for (inst, cls) in inst_types]
        result = []
        for relevant in itertools.product(*pool):
            tosubs = []
            for i, (inst, types) in enumerate(inst_types):
                tosubs.append((inst, self.insts[relevant[i]]))
            print "Here is the one to sub: %s" % tosubs
            result.append(substitute(expr, *tosubs))    
        return result
    
    def g_prpg(self, inst, type, expr):
        return self.g_prpg_multi([(inst, type)], expr)
    
    def g_ifalive(self, inst, type, expr):
        leaves = [self.types[x] for x in self.children_leaf_classes[str(type)]]
        new_expr = Implies(
                           True,#self.alive(inst),
                           Implies(
                                   _Or([self.typeof(inst)==cls for cls in leaves]),
                                   expr
                                   )
                          ) 
        return self.g_prpg(inst, type, new_expr)
    def g_forall(self, inst_types, expr):
        return _And(self.g_prpg_multi(inst_types, expr))
    
    def g_exist(self, inst_types, expr):
        return _Or(self.g_prpg_multi(inst_types, expr))
    
    def g_sum(self, inst, type, attr, condition):
        new_expr = If(condition, attr(inst), 0)
        return Sum(self.g_prpg(inst, type, new_expr))
    
    def g_ifalive_exists(self, ifinst, iftype, ifexp, exinst, extype, expr):
        new_expr = self.g_exist([(exinst, extype)], And(self.typeof(exinst)==extype, expr))
        return self.g_ifalive(ifinst, iftype, Implies(ifexp, new_expr))
   
   
   
   
class ChangeDriver():
    def __init__(self, smt, fixed_soft = []):
        self.smt = smt
        self.cd = smt.cd
        self.fixed_soft = [x for x in fixed_soft]
        self.monitored = []
        self.new_soft = []
    
    def init_fixed_soft(self, solver):
        self.fixed_soft = [x for x in solver.soft]
        
    def add_fixed_soft(self, cst, weight):
        self.fixed_soft.append((cst, weight)) 
        
    def add_new_soft(self, cst, weight):
        self.new_soft.append((cst, weight))
    
    def add_monitored(self, property, weight):
        self.monitored.append((property, weight))
    
    def start_over(self, solver):
        meval = solver.model().eval
        self.new_soft = []
        for property, weight in self.monitored:
            fun = None
            relev = None
            if property == 'alive':
                fun = self.smt.alive
                relev = set(self.smt.insts.keys()) - set(['null'])
            else:
                fun = self.smt.funcs[property]
                cls = None
                if property in self.cd.attr:
                    cls = self.cd.attr[property][0]
                elif property in self.cd.ref:
                    cls = self.cd.ref[property][0]
                relev = self.smt.get_potential_instances(cls)
            for inst in relev:
                ins = self.smt.insts[inst]
                real_weight = weight
                if isinstance(weight, tuple):
                    v, expr = weight
                    new_expr = substitute(expr, (v, ins))
                    x = meval(new_expr)
                    #print "=====>%s:%s:%s"%(ins, new_expr, x)
                    real_weight = int(str(x))
                self.add_new_soft( fun(ins) == meval(fun(ins)), real_weight )
                
        solver.soft = self.fixed_soft + self.new_soft
        
            
class QuickExpr:
    def __init__(self, alive, typeof, nullinst, nulltype):
        self.alive = alive
        self.typeof = typeof
        self.nullinst = nullinst
        self.nulltype = nulltype
        
    def only_alive(self, inst, expr):
        return Implies(self.alive(inst), expr)
    
    def only_alive_type(self, inst, ttype, expr):
        return Implies(And(self.alive(inst), self.typeof(inst)==ttype), expr)
    
    def only_alive_types(self, inst, types, expr):
        return Implies(And(self.alive(inst), Or([self.typeof(inst)==t for t in types])), expr)
    
    def alter_types(self, inst, types):
        return Implies(self.alive(inst), Or([self.typeof(inst)==type for type in types]))
    
    def cartesian_not_equal(self, instances, types):
        return And([self.typeof(x)!=y for x in instances for y in types])
    
    def count(self, insts, target, relation):
        return Sum([If(relation(i)==target, 1, 0) for i in insts])
    
    def count_sum(self, insts, target, relation, attr):
        return Sum([If(relation(i)==target, attr(i), 0) for i in insts])
    
    def type_dep(self, inst, reference, sourceType, targetTypes):
        return Implies(And(self.alive(inst), self.typeof(inst)==sourceType), 
                       And(
                           self.alive(reference(inst)),
                           Or([self.typeof(reference(inst))==t for t in targetTypes])
                       ))
        
    def type_dep_multiple(self, inst, reference, sourceTypes, targetTypes):
        return Implies(And(self.alive(inst), Or([self.typeof(inst)==t for t in sourceTypes])), 
                       And(
                           self.alive(reference(inst)),
                           Or([self.typeof(reference(inst))==t for t in targetTypes])
                       )) 
           
    def ref_to_null(self, inst, reference, sourceType):
        return Implies(self.typeof(inst)==sourceType, reference(inst)==self.nullinst)
    
    def ref_to_null_multiple(self, inst, reference, sourceTypes):
        return Implies(Or([self.typeof(inst)==t for t in sourceTypes]),
                       reference(inst)==self.nullinst)
        
    def exist_alive_typed(self, instances, types):
        return Or([And(self.alive(i), Or([self.typeof(i)==t for t in types])) for i in instances])
    