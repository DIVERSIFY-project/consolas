'''
Created on 3 Feb 2015

@author: Hui Song
'''
import unittest
from model_util import *
from softz3_msopt import *
from softz3_opt import *
from softz3_diagnose import *
from model_painter import *
from model_cloudml import *
from time import clock

class Test(unittest.TestCase):


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
        cd.define_class('EC2Free', ['Vm'])
                        
        cd.define_class("Deployable")
        
        cd.define_class("Web", ['Deployable'])
        
        cd.define_class("Lb", ['Deployable'])
                
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
        cd.define_ref('lb', 'Web', 'Lb', True)
        
        cd.define_attr_int('vmem', 'Vm', 1, 10)
        cd.define_attr_int('rmem', 'Deployable', 1, 5)
        cd.define_attr_int('port', 'Web', 8081, 9000)
        
        cd.define_attr_bool('fast', 'Web')
        cd.define_attr_bool('noise', 'Web')
        cd.define_attr_bool('pollution', 'Web')
        cd.define_attr_bool('cheap', 'Web')
        
        
        smt = ModelSMT(cd)
        smt.maxinst["Azure"] = 5
        smt.maxinst["EC2"] = 5
        #smt.maxinst["Hopper"] = 1
        smt.maxinst["FastCH"] = 1
        smt.maxinst['Hopper'] = 2
        smt.maxinst["PaaSRedis"] = 2
        smt.maxinst["LocalRedis"] = 2
        #smt.maxinst["CarHopper"] = 1
        smt.maxinst["Web"] = 4
        smt.maxinst['Sensor']=2
        smt.maxinst['Lb'] = 1
        #smt.maxinst["SlowCH"] = 2
        
        smt.generate()
        
        #These variables are used only to shortant the constraint definitions
        x = smt.gen_const_inst()
        y = smt.gen_const_inst()
        z = smt.gen_const_inst()
        db = smt.funcs['db']
        sdb = smt.funcs['sdb']
        hp = smt.funcs['hp']
        vmem = smt.funcs['vmem']
        rmem = smt.funcs['rmem']
        deploy = smt.funcs['deploy']
        Azure = smt.types['Azure']
        Hopper = smt.types['Hopper']
        FastCH = smt.types['FastCH']
        Web = smt.types['Web']
        Sensor = smt.types['Sensor']
        Pollution = smt.types['PollutionSensor']
        Noise = smt.types['NoiseSensor']
        typeof = smt.typeof
        alive = smt.alive
        web = smt.insts['web00']
        web1 = smt.insts['web01']
        fast = smt.funcs['fast']
        pollution = smt.funcs['pollution']
        noise = smt.funcs['noise']
        port = smt.funcs['port']
        
        #for cst, comment in smt.hard_const:
        #    print "%s: %s" %(cst, comment)
        
        
        painter = ModelPainter(smt)
        
        cdriver = ChangeDriver(smt)
        cdriver.add_monitored('deploy', 100)
        cdriver.add_monitored('alive', (x, If(alive(x), 10, 20)))
        cdriver.add_monitored('db', 10)
        cdriver.add_monitored('sdb', 10)
        
        cloudml = CloudML(smt)
        cloudml.attr = ['port']
        cloudml.host = [('deploy', 'ubuntuReq', 'ubuntuPrv')]
        cloudml.relation = [('db', 'redisReq', 'redisPrv'), ('sdb', 'redisReq', 'redisPrv'), ('hp', 'hopperReq', 'hopperPrv')]
        cloudml.rev_relation = [('lb', 'lbReq', 'lbPrv')]
        cloudml.vm = ['Vm']
        cloudml.internal = ['Deployable']
        cloudml.external = ['PaaSRedis']
        
        solver = SoftSolverMsOpt()
        for cst, comment in smt.hard_const:
                solver.add_hard(cst)
        

                
        #Hate Azure, for no reason
        for cst in smt.g_prpg(x, Azure, typeof(x)!=Azure):
            solver.add_soft(cst, 100)
            
        solver.add_soft(smt.alive(web), 1000)
        #solver.add_soft(smt.typeof(smt.insts['carHopper00'])==smt.types['FastCH'], 50)
        for cst in smt.g_type_dep("db", ["CarHopper"], ["LocalRedis"]):
            solver.add_soft(cst, 100)
            #solver.add_hard(cst)
            
        for cst in smt.g_type_dep('deploy', ['FootHopper', 'FastCH'], ['Azure']):
            solver.add_soft(cst, 100)        
        
        
        # distinguised hopper
        solver.add_hard(smt.g_forall([(x, Web), (y, Web)], Implies(And(hp(x)==hp(y), alive(hp(x))), x==y)))        
        
        # distinguised port
        solver.add_hard(smt.g_forall([(x, Web), (y, Web)], Implies(And([alive(x), alive(y), port(x)==port(y)]), x==y)))        
        
        
        solver.add_hard(smt.g_ifalive(x, smt.types['FastCH'], smt.g_exist([(y, smt.types['Sensor'])], db(x)==sdb(y))))                
        expr = smt.g_ifalive(x,smt.types['Hopper'], rmem(x)==5)
        solver.add_hard(expr)
        solver.add_hard(smt.g_ifalive(x,smt.types['Sensor'], rmem(x)==5))
        solver.add_hard(smt.g_ifalive(x,smt.types['LocalRedis'], rmem(x)==2))
        solver.add_hard(smt.g_ifalive(x, smt.types['Lb'], rmem(x)==1))
        solver.add_hard(smt.g_ifalive(x, smt.types['Vm'], vmem(x)==9))
        
        
        solver.add_hard(And(smt.g_ifalive(y, smt.types['Vm'], vmem(y) >= smt.g_sum(x, smt.types['Deployable'], rmem, deploy(x)==y))))
        
        #context rule
        solver.add_hard(And(smt.g_ifalive(x, Web, Implies(fast(x), typeof(hp(x))==FastCH) )))
        solver.add_hard(And(smt.g_ifalive(x, Web, Implies(pollution(x), smt.g_exist([(y, Pollution)], And(typeof(y)==Pollution, sdb(y)==db(hp(x))))))))
        solver.add_hard(And(smt.g_ifalive_exists(x, Web, noise(x), y, Noise, sdb(y)==db(hp(x)))))
        
        #eclusive sensor for FastCH
        expr = smt.g_forall([(y, Sensor), (z, Sensor)], Implies(And(sdb(y)==db(x), sdb(z)==db(x)), y==z))
        solver.add_hard(And(smt.g_ifalive(x, FastCH, expr)))
        
        cdriver.init_fixed_soft(solver)

        for i in smt.insts.itervalues():
            if (not str(i).startswith('web00')) and str(i)!='null':
                solver.add_soft(Not(smt.alive(i)), 10)
        
        
        self.do_search(solver)
        #print solver.last_sat()
        painter.eval = solver.model().eval
        
        print solver.get_broken()
        print solver.get_broken_weight()
        cloudml.meval = solver.model().eval
        print cloudml.generate_instances()
        painter.make_graph()
        

        for i in range(0,100):
            try:
                cdriver.start_over(solver)
                for cst, weight, perm in self.console_input():
                    solver.add_soft(eval(cst), weight)
                    if perm:
                        cdriver.add_fixed_soft(eval(cst), weight)
                    #print eval(cst)
                self.do_search(solver)
                print solver.get_broken()
                for i in smt.insts.itervalues():
                    if str(i).startswith('web') and str(solver.model().eval(alive(i)))=='True':
                        print 'Port of %s: %s' % (i, solver.model().eval(port(i)))
                meval = solver.model().eval
                painter.eval = meval
                cloudml.meval = meval
                print cloudml.generate_instances()
                painter.make_graph()
            except:
                print "Unexpected error:", sys.exc_info()[0]
        
    def do_search(self, solver):
        solver.init_solver()
        
        print "start searching"        
        (result, time) = solver.search_with_timing()
        print '%s: %.4f'%(result,time)
        
    def console_input(self, monitor = None):
        result = []
        for j in range(0,100):
            perm = False
            s = raw_input('(constraint[ | weight [ | !] ]) | go | quit>>')
            if s == 'quit' or s == 'q':
                quit()
            if s == 'go':
                break
            if '|' in s:
                conswei = s.split('|')
                print conswei[0].strip()
                if len(conswei) >= 3 and ('perm' == conswei[2].strip() or '!' == conswei[2].strip()):
                   perm = True 
                result.append((conswei[0].strip(), int(conswei[1].strip()), perm))
                
            else:
                result.append((s.strip(), 10000, perm))
        return result
        
    
if __name__ == "__main__":
    #import sys;sys.argv = ['', 'Test.testClassDiagram']
    unittest.main()