'''
Created on 3 Feb 2015

@author: fafey
'''
import unittest
from model_util import *

class Test(unittest.TestCase):


    def ttestReference(self):
        fun = Function('fun', IntSort(), IntSort())
        print fun

    def testClassDiagram(self):
        cd = ClassDiagram('SmartGH')
        cd.define_class("Vm")
        cd.define_class("Deployable")
        cd.define_class("Hopper", ['Deployable'])
        cd.define_class("Web", ['Deployable'])
        cd.define_class("FastHopper",["Hopper"])
        cd.define_class("SlowHopper",["Hopper"])
        cd.define_class("GoodHopper",["Hopper"])
        cd.define_class("FastGoodHopper",["GoodHopper"])
        cd.define_class("SlowGoodHopper",["GoodHopper"])
        
        cd.define_ref('deploy', 'Deployable', 'Vm')
        
        
        smt = ModelSMT(cd)
        smt.maxinst["Vm"] = 3
        smt.maxinst["Hopper"] = 2
        smt.maxinst["SlowGoodHopper"] = 2
        
        smt.generate()
        
        print smt.types
        print smt.insts
        print smt.hard_const
        print smt.funcs
        

    
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