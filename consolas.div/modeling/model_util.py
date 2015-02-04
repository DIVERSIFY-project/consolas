from z3 import *

downcasefirst = lambda s: s[:1].lower() + s[1:] if s else ''

class ClassNotDefined:
    def __init__(self, name):
        self.name = name
        
    def __repr__(self):
        return "<%s>" % self.name

class ClassDiagram:
    def __init__(self, name):
        self.name = name;
        self.classes = set()
        self.superclass = dict()
        self.ref = dict()
        self.multiref = dict()
        
        
    def define_class(self, class_name, supper_class = []):
        if supper_class == None or len(supper_class)==0:
            self.classes.add(class_name)
        else:
            if any(not(x in self.classes) for x in supper_class):
                raise ClassNotDefined("One of the supper classes of %s" % class_name)
            self.classes.add(class_name)
            self.superclass[class_name] = supper_class
            
    def define_ref(self, name, fromclass, toclass):
        if not (fromclass in self.classes) :
            raise ClassNotDefined(fromclass)
        if not (toclass in self.classes) :
            raise ClassNotDefined(toclass)
        self.ref[name] = (fromclass, toclass)
        
        
        
class ModelSMT:
    def __init__(self, class_diagram):
        self.cd = class_diagram
        self.maxinst = dict()  # max number of instances for each type
        self.inst_by_type = dict()
        self.nullinst = None
        
        self.types = dict()
        self.insts = dict()
        self.funcs = dict()
        self.indirect_super_class = None
        self.indirect_insts = None
        self.leaf_classes = None
        self.children_leaf_classes = None
        
        self.hard_const = []
        
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
        self.children_leaf_classes = clsleafch
        
        CompType, comp_types = EnumSort("CompType", ["NullType"]+class_names)
        inst_names = []
        direct_type = dict()
        indirect_insts = dict([(c, set()) for c in class_names])
        for cname in class_names:
            inum = self.maxinst.get(cname, 0)
            cname_lower = downcasefirst(cname)
            local_inst_names = ["%s%02d" % (cname_lower, i) for i in range(0, inum) ]
            for i in local_inst_names:
                direct_type[i] = cname
                for c in set([cname]) | insupc[cname]:
                    indirect_insts[c].add(i) 
            inst_names = inst_names + local_inst_names
        self.indirect_insts = indirect_insts   
            
        CompInst, comp_insts = EnumSort("CompInst", ['null'] + inst_names)
        nullinst = comp_insts[0]
        NullType = comp_types[0]
        
        for ct in comp_types : self.types[str(ct)] = ct
        for ci in comp_insts : self.insts[str(ci)] = ci
        
        typeof = Function('typeof', CompInst, CompType)
        alive = Function('alive', CompInst, BoolSort())   
        
        hard = self.hard_const
        hard.append(typeof(nullinst) == NullType)
        hard.append(alive(nullinst) == False)
        
        #constraints for types
        for instn, inst in self.insts.iteritems():
            if instn == 'null':
                continue
            leaves = clsleafch[direct_type[instn]]
            if len(leaves)==1:
                hard.append(typeof(inst)==self.types[next(iter(leaves))])
            else:
                hard.append( Or([typeof(inst)==self.types[t] for t in leaves ]) )
        
        refs = [Function(fn, CompInst, CompInst) for fn in self.cd.ref.iterkeys()]
        for fun in refs: self.funcs[str(fun)] = fun
        
    

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
    