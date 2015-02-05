'''
Created on 3 Feb 2015

@author: fafey
'''
import unittest
from model_util import *
from softz3_msopt import *
from softz3_opt import *
from softz3_diagnose import *
from model_painter import *

class Test(unittest.TestCase):


    def ttestReference(self):
        fun = Function('fun', IntSort(), IntSort())
        x = dict()
        #x.v
        print fun

    def testZ3Ms(self):
        solver = SoftSolverMsOpt()
        x = Int('x')
        y = Int('y')
        
        solver.add_hard(y==1)
        solver.add_soft(x>1, 4)
        solver.add_soft(x>2, 3)
        solver.add_soft(x<0, 6)
        solver.add_soft(y==1, 2)
        solver.init_solver()
        solver.search()
        print solver.model()

    def testClassDiagram(self):
        cd = ClassDiagram('SmartGH')
        cd.define_class("Vm")
        cd.define_class("Deployable")
        
        cd.define_class("Web", ['Deployable'])
        
        cd.define_class("Hopper", ['Deployable'])        
        cd.define_class("FastHopper",["Hopper"])
        cd.define_class("SlowHopper",["Hopper"])
        cd.define_class("CarHopper",["Hopper"])
        cd.define_class("FastCH",["CarHopper"])
        cd.define_class("SlowCH",["CarHopper"])
        
        cd.define_class("Redis")
        cd.define_class("LocalRedis", ["Redis","Deployable"])
        cd.define_class("PaaSRedis", ["Redis"])
        
        cd.define_ref('deploy', 'Deployable', 'Vm', True)
        cd.define_ref('db', 'Hopper', 'Redis', True)
        
        
        smt = ModelSMT(cd)
        smt.maxinst["Vm"] = 2
        smt.maxinst["Hopper"] = 2
        smt.maxinst["Redis"] = 2
        #smt.maxinst["SlowCH"] = 2
        
        smt.generate()
        
        print smt.types
        print smt.insts
        for cst, comment in smt.hard_const:
            print "%s: %s" %(cst, comment)
        print smt.funcs
        print "children-leaves:" + str(smt.children_leaf_classes)
        
        painter = ModelPainter(smt)
        
        solver = SoftSolverMsOpt()
        #solver = SoftSolverDiagnose()
        
        for cst, comment in smt.hard_const:
            #if comment != "ref-right-codomain":
                solver.add_hard(cst)
        
        for i in smt.insts.itervalues():
            if str(i)!='hopper00' and str(i)!='null':
                solver.add_soft(Not(smt.alive(i)), 10)
            
        solver.add_soft(smt.alive(smt.insts['hopper00']), 30)
        
        #solver.add_hard(smt.alive(smt.insts['hopper00']))
        #solver.add_hard(Not(smt.alive(smt.insts['hopper00'])))
        #solver.add_soft(smt.alive(smt.insts['hopper01']), 100)
        solver.add_soft(smt.typeof(smt.insts['redis00'])==smt.types['LocalRedis'],30)
        #solver.add_hard(smt.alive(smt))
        
        solver.init_solver()
        #print solver.soft
        #print solver.solver
        print "start searching"
        #solver.solver.help()
        solver.search()
        #print solver.last_sat()
        painter.eval = solver.model().eval
        
        print solver.get_broken()
        print solver.get_broken_weight()
        
        print painter.eval(smt.typeof(smt.insts['hopper00']))
        print painter.eval(smt.alive(smt.insts['hopper00']))
        painter.make_graph()
        
    def ttestIndirectSuperClass(self):
        cd = ClassDiagram('SmartGH')
        cd.define_class('A')
        cd.define_class('B')
        cd.define_class('C', ['A','B'])
        cd.define_class('D', ['A'])
        cd.define_class('E', ['C'])
        cd.define_class('F', ['D', 'E'])
        cd.define_class('G', ['C'])
        cd.define_class('H', ['D'])
        
        
        
        smt = ModelSMT(cd)
        smt.maxinst['F']= 3
        smt.maxinst['C']= 1
        smt.generate()
        
        print smt.leaf_classes
        print smt.indirect_super_class
        print smt.indirect_insts
        print smt.children_leaf_classes
    
if __name__ == "__main__":
    #import sys;sys.argv = ['', 'Test.testClassDiagram']
    unittest.main()