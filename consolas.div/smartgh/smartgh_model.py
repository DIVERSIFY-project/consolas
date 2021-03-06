from model_util import *
from softz3 import *
from softz3_msopt import *
from model_painter import *
from model_cloudml import *
from smartgh_util import *

cd = ClassDiagram('SmartGH')

cd.define_class("Vm")
cd.define_class("EC2", ['Vm'])
cd.define_class("OpenStackLarge", ['Vm'])
cd.define_class('OpenStackHuge', ['Vm'])
                
cd.define_class("Deployable")

cd.define_class("Web", ['Deployable'])
cd.define_class("Lb", ['Deployable'])
        
cd.define_class("Hopper", ['Deployable'])        
cd.define_class("CarHopper", ["Hopper"])
cd.define_class("FastCH", ["CarHopper"])
cd.define_class("NormalCH", ["CarHopper"])
cd.define_class("FootHopper", ["Hopper"])
cd.define_class("BasicHopper", ["Hopper"])

cd.define_class("Redis")
cd.define_class("LocalRedis", ["Redis","Deployable"])
cd.define_class("PaaSRedis", ["Redis"])

cd.define_class('Sensor', ['Deployable'])
cd.define_class('NoiseSensor', ['Sensor'])
cd.define_class('PollutionSensor', ['Sensor'])
#cd.define_class('TrafficSensor', ['Sensor'])

cd.define_ref('deploy', 'Deployable', 'Vm', True)
cd.define_ref('db', 'Hopper', 'Redis', True)
cd.define_ref('hp', 'Web', 'Hopper', True)
cd.define_ref('sdb', 'Sensor', 'Redis', True)
cd.define_ref('lb', 'Web', 'Lb', False)

cd.define_attr_int('vmem', 'Vm', 1, 10)
cd.define_attr_int('rmem', 'Deployable', 0, 5)
cd.define_attr_int('port', 'Web', 8081, 8089)
cd.define_attr_int('hport', 'Hopper', 8090, 8099)

cd.define_attr_bool('fast', 'Web')
cd.define_attr_bool('noise', 'Web')
cd.define_attr_bool('pollution', 'Web')
cd.define_attr_bool('cheap', 'Web')


smt = ModelSMT(cd)

smt.maxinst["Vm"] = 3
smt.maxinst["OpenStackHuge"] = 1
smt.maxinst["FastCH"] = 1
smt.maxinst['Hopper'] = 4
smt.maxinst["PaaSRedis"] = 2
smt.maxinst["LocalRedis"] = 3
smt.maxinst["Web"] = 5
smt.maxinst['Sensor']=3
smt.maxinst['Lb'] = 1


smt.generate()

#for cst, comment in smt.hard_const:
#    print "%s: %s" %(cst, comment)

#These variables are used only to shorthant the constraint definitions
x = smt.gen_const_inst()
y = smt.gen_const_inst()
z = smt.gen_const_inst()
db = smt.funcs['db']
sdb = smt.funcs['sdb']
hp = smt.funcs['hp']
vmem = smt.funcs['vmem']
rmem = smt.funcs['rmem']
deploy = smt.funcs['deploy']
OpenStackLarge = smt.types['OpenStackLarge']
BasicHopper = smt.types['BasicHopper']
FootHopper = smt.types['FootHopper']
Hopper = smt.types['Hopper']
CarHopper = smt.types['CarHopper']
FastCH = smt.types['FastCH']
NormalCH = smt.types['NormalCH']
PaaSRedis = smt.types['PaaSRedis']
LocalRedis = smt.types['LocalRedis']
Web = smt.types['Web']
Sensor = smt.types['Sensor']
Pollution = smt.types['PollutionSensor']
Noise = smt.types['NoiseSensor']
typeof = smt.typeof
alive = smt.alive
web = smt.insts['web00']
web1 = smt.insts['web01']
web00 = smt.insts['web00']
web01 = smt.insts['web01']
fast = smt.funcs['fast']
pollution = smt.funcs['pollution']
noise = smt.funcs['noise']
port = smt.funcs['port']
hport = smt.funcs['hport']
hopper00 = smt.insts['hopper00']
hopper01 = smt.insts['hopper01']
hopper02 = smt.insts['hopper02']
hopper03 = smt.insts['hopper03']
lb = smt.funcs['lb']
EC2 = smt.types['EC2']
OpenStackHuge = smt.types['OpenStackHuge']
#shorthands end here

_t = lambda name : smt.types[name]
_i = lambda name : smt.insts[name]
#auxiliary objects to display the result (painter), monitor change (cdriver), 
#and generate CloudML scripts

painter = ModelPainter(smt)

cdriver = ChangeDriver(smt)
cdriver.add_monitored('deploy', 10)
cdriver.add_monitored('alive', (x, If(alive(x), 1, 30)))
cdriver.add_monitored('db', 10)
cdriver.add_monitored('sdb', 10)

cloudml = CloudML(smt)
cloudml.attr = ['port', 'hport']
cloudml.host = [('deploy', 'ubuntuReq', 'ubuntuPrv')]
cloudml.relation = [('db', 'redisReq', 'redisPrv'), ('sdb', 'redisReq', 'redisPrv'), ('hp', 'hopperReq', 'hopperPrv')]
cloudml.rev_relation = [('lb', 'lbReq', 'webPrv')]
cloudml.vm = ['Vm']
cloudml.internal = ['Deployable']
cloudml.external = ['PaaSRedis']
cloudml.tags={'FastCH':'fast', 'NormalCH':'car', 'FootHopper':'foot', 'BasicHopper':'default'}

diversifyer = Diversifyer(smt, cdriver)
diversifyer.add_repo('Hopper')
diversifyer.add_repo('Sensor')
#end of auxiliary

'''
' Create the main solver, and put the meta-model-related constraints
' into it
'''
solver = SoftSolverMsOpt()
for cst, comment in smt.hard_const:
        solver.add_hard(cst)



#Hate PaaSRedis, because we don't support it
for cst in smt.g_prpg(x, PaaSRedis, typeof(x)!=PaaSRedis):
    solver.add_soft(cst, 300)          
#Hate EC2, because we don't support it, too
for cst in smt.g_prpg(x, EC2, typeof(x)!=EC2):
    solver.add_soft(cst, 100)
#Hate OpenStackHuge as well, because it's huge    
for cst in smt.g_prpg(x, OpenStackHuge, typeof(x)!=OpenStackHuge):
    solver.add_soft(cst, 100)



#At least one web by default    
solver.add_soft(smt.alive(web), 1000)

#CarHopper prefers LocalRedis
for cst in smt.g_type_dep("db", ["CarHopper"], ["LocalRedis"]):
    solver.add_soft(cst, 100)
    #solver.add_hard(cst)     


# distinguised hopper: each web
#solver.add_hard(smt.g_forall([(x, Web), (y, Web)], Implies(And(hp(x)==hp(y), alive(hp(x))), x==y)))        

# distinguised port
solver.add_hard(smt.g_forall([(x, Web), (y, Web)], Implies(And([alive(x), alive(y), port(x)==port(y)]), x==y))) 
# more than one web? call a load balance!
solver.add_hard(smt.g_forall([(x, Web), (y, Web)], Implies(And([alive(x), alive(y), x!=y]), And(alive(lb(x)), alive(lb(y))))))       
# Two hoppers cannot be deployed with the same port
solver.add_hard(smt.g_forall([(x,Hopper), (y, Hopper)], Implies(And([alive(x), alive(y), hport(x)==hport(y)]), x==y)))
# and two redis as well (because of the port)
solver.add_hard(smt.g_forall([(x,LocalRedis), (y, LocalRedis)], Implies(And([alive(x), alive(y), deploy(x)==deploy(y)]), x==y)))
#each hopper should be covered by a web
exps = smt.g_ifalive_exists(x, Hopper, True, y, Web, hp(y)==x)
solver.add_hard(And(exps))
#Hoppers except Basic should have a sensor
exp = And(smt.g_ifalive(x, FootHopper, smt.g_exist([(y, Sensor)], sdb(y) == db(x))))
print '=======%s' % exp
solver.add_hard(exp)
solver.add_hard(And(smt.g_ifalive(x, CarHopper, smt.g_exist([(y, Sensor)], sdb(y) == db(x)))))

solver.add_hard(smt.g_ifalive(x, smt.types['FastCH'], smt.g_exist([(y, smt.types['Sensor'])], db(x)==sdb(y))))                
solver.add_hard(smt.g_ifalive(x, smt.types['Web'], rmem(x)==1))
solver.add_hard(smt.g_ifalive(x, smt.types['FootHopper'], rmem(x)==1))
solver.add_hard(smt.g_ifalive(x, smt.types['CarHopper'], rmem(x)==2))
solver.add_hard(smt.g_ifalive(x, smt.types['Sensor'], rmem(x)==1))
solver.add_hard(smt.g_ifalive(x, smt.types['LocalRedis'], rmem(x)==1))
solver.add_hard(smt.g_ifalive(x, smt.types['Lb'], rmem(x)==1))
solver.add_hard(smt.g_ifalive(x, smt.types['OpenStackHuge'], vmem(x)==8))
solver.add_hard(smt.g_ifalive(x, smt.types['OpenStackLarge'], vmem(x)==4))


solver.add_hard(And(smt.g_ifalive(y, smt.types['Vm'], vmem(y) >= smt.g_sum(x, smt.types['Deployable'], rmem, deploy(x)==y))))

#context rule
solver.add_hard(And(smt.g_ifalive(x, Web, Implies(fast(x), typeof(hp(x))==FastCH) )))
solver.add_hard(And(smt.g_ifalive(x, Web, Implies(pollution(x), smt.g_exist([(y, Pollution)], And(typeof(y)==Pollution, sdb(y)==db(hp(x))))))))

solver.add_hard(And(smt.g_ifalive_exists(x, Web, noise(x), y, Noise, sdb(y)==db(hp(x)))))

#eclusive sensor for FastCH
expr = smt.g_forall([(y, Sensor), (z, Sensor)], Implies(And(sdb(y)==db(x), sdb(z)==db(x)), y==z))
solver.add_hard(And(smt.g_ifalive(x, FastCH, expr)))

theweb = Const('theweb', smt.CompInst)
solver.add_hard(Or(smt.g_exist([(x, Web)], And(alive(x), x==theweb))))

cdriver.init_fixed_soft(solver)

for i in smt.insts.itervalues():
    if (not str(i).startswith('web00')) and str(i)!='null':
        solver.add_soft(Not(smt.alive(i)), 10)



do_search(solver)

painter.eval = solver.model().eval

print solver.get_broken()
print solver.get_broken_weight()
cloudml.meval = solver.model().eval
print cloudml.generate_instances()
painter.make_graph()


for i in range(0,100):
    #try:
        cdriver.start_over(solver)
        command = console_input()
        if command == 'quit':
            quit()
        elif command == 'diversify grow':
            #for n in range(0,3):
            diversifyer.diversify_grow_run(solver)
        else:
            for cst, weight, perm in command:
                solver.add_soft(eval(cst), weight)
                if perm:
                    cdriver.add_fixed_soft(eval(cst), weight)
            #print eval(cst)
        #print "which zero: %s" % [x for x in solver.soft if x[1] == 0]
            do_search(solver)
        
        meval = solver.model().eval
        painter.eval = meval
        cloudml.meval = meval
        print cloudml.generate_instances()
        print 'Total cost: %d, %s' %(solver.get_broken_weight(),solver.get_broken())
        #print meval()
        painter.make_graph()
    #except:
        s = str(sys.exc_info())
        print "Unexpected error:%s" % s
        if 'on closed file' in s:
            quit()










