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

    def ttestZ3Ms(self):
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
    
    def ttestAlive(self):
        
        solver = Optimize()
        Inst, (n, x, y, z) = EnumSort('Inst', ['n', 'x', 'y', 'z'])
        
        alive = Function('alive', Inst, BoolSort())
        solver.add(Not(alive(n)))        
        solver.add(Implies(alive(x), alive(y)))
        
        for i in [n, x, y, z]:
            solver.add_soft(Not(alive(i)), 1)
        
        #solver.add(alive(x))
        solver.add_soft(alive(x), 5)
        
        print solver.check().r
        print solver.model()
        
    def testClassDiagram(self):
        cd = ClassDiagram('SmartGH')
        cd.define_class("Vm")
        cd.define_class("EC2", ['Vm'])
        cd.define_class("Azure", ['Vm'])
                        
        cd.define_class("Deployable")
        
        cd.define_class("Web", ['Deployable'])
                
        cd.define_class("Hopper", ['Deployable'])        
        cd.define_class("CarHopper", ["Hopper"])
        cd.define_class("FastCH", ["CarHopper"])
        cd.define_class("SlowCH", ["CarHopper"])
        cd.define_class("FootHopper", ["Hopper"])
        cd.define_class("BasicHopper", ["Hopper"])
        
        cd.define_class("Redis")
        cd.define_class("LocalRedis", ["Redis","Deployable"])
        cd.define_class("PaaSRedis", ["Redis"])
        
        cd.define_class('Sensor', ['Deployable'])
        cd.define_class('NoiseSensor', ['Sensor'])
        cd.define_class('PollutionSensor', ['Sensor'])
        cd.define_class('TrafficSensor', ['Sensor'])
        
        
        
        cd.define_ref('deploy', 'Deployable', 'Vm', True)
        cd.define_ref('db', 'Hopper', 'Redis', True)
        cd.define_ref('hp', 'Web', 'Hopper', True)
        cd.define_ref('sdb', 'Sensor', 'Redis', True)
        
        cd.define_attr_int('vmem', 'Vm', 1, 10)
        cd.define_attr_int('rmem', 'Deployable', 1, 5)
        
        smt = ModelSMT(cd)
        smt.maxinst["Vm"] = 4
        smt.maxinst["Hopper"] = 2
        smt.maxinst["Redis"] = 2
        smt.maxinst["CarHopper"] = 1
        smt.maxinst["Web"] = 1
        smt.maxinst['Sensor']=2
        #smt.maxinst["SlowCH"] = 2
        
        smt.generate()
        
        print smt.hard_const
        
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
                solver.add_hard(cst)
        
        for i in smt.insts.itervalues():
            if str(i)!='web00' and str(i)!='null':
                solver.add_soft(Not(smt.alive(i)), 10)
                
        for i in smt.insts:
            if i != 'null':
                solver.add_soft(smt.typeof(smt.insts[i])!=smt.types['Azure'], 1)
            
        solver.add_soft(smt.alive(smt.insts['web00']), 1000)
        #solver.add_soft(smt.typeof(smt.insts['carHopper00'])==smt.types['FastCH'], 50)
        for cst in smt.gen_type_dep("db", ["CarHopper"], ["LocalRedis"]):
            solver.add_soft(cst, 100)
            
        for cst in smt.gen_type_dep('deploy', ['FootHopper', 'FastCH'], ['Azure']):
            solver.add_soft(cst, 100)
        
        x = smt.gen_const_inst()
        y = smt.gen_const_inst()
        db = smt.funcs['db']
        sdb = smt.funcs['sdb']
        vmem = smt.funcs['vmem']
        rmem = smt.funcs['rmem']
        deploy = smt.funcs['deploy']
        
        mustfast = smt.gen_propagate([(x, smt.types['Hopper'])], 
                                             Or(smt.typeof(x)==smt.types['FastCH'], Not(smt.alive(x)))
                                             )
        print mustfast
        for cst in mustfast:
            solver.add_soft(cst, 1000)
        
        solver.add_hard(
                        smt.gen_forall([(x, smt.types['Hopper'])],
                                       Implies(
                                               smt.typeof(x)==smt.types['FastCH'],
                                               smt.gen_exist(
                                                             [(y, smt.types['Sensor'])], 
                                                             db(x) == sdb(y)
                                                        )
                                           )
                                       )
                        )
                        
        
        solver.add_hard(smt.gen_if_alive_type(x,smt.types['Hopper'], rmem(x)==5))
        solver.add_hard(smt.gen_if_alive_type(x,smt.types['Sensor'], rmem(x)==5))
        solver.add_hard(smt.gen_if_alive_type(x,smt.types['LocalRedis'], rmem(x)==2))
        solver.add_hard(smt.gen_if_alive_type(x, smt.types['Vm'], vmem(x)==9))
        
        
        solver.add_hard(And(smt.gen_if_alive_type(y, smt.types['Vm'], vmem(y) >= smt.gen_sum(x, smt.types['Deployable'], rmem, deploy(x)==y))))
        
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