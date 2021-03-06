'''
Created on 12 Nov 2013

@author: fafey
'''

from z3 import *
from random import randint
from time import clock
from softz3 import *
import unittest


class SoftSolverMsOpt(SoftSolver):
    
    
    def __init__(self):
        SoftSolver.__init__(self)
        self.error = 50
    
    def init_solver(self):
        
        self.solver = Optimize()
        
        for cst in self.hard:
            self.solver.add(cst)
        for i, (cst, wt) in enumerate(self.soft):
            if wt == 0: rwt =1
            else: rwt = wt
            self.solver.add_soft(cst, rwt)
            #print self.solver.v
        
      

    def search(self):
        #self.solver.set('engine', 'symba')
        #self.solver.set('maxsat_engine', 'sls')
        #self.solver.set('enable_sat', True)
        #self.solver.set('enable_sls', True)
        self.solver.set('optsmt_engine', 'farkas')
        self.solver.set('maxres.hill_climb', False)
        
        self._last_result = self.solver.check().r
        self._last_model = self.solver.model()
        
  
            
    