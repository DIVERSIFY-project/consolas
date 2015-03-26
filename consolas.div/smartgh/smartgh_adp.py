from model_util import *
from softz3 import *
from softz3_msopt import *
from model_painter import *
from model_cloudml import *
from smartgh_util import *

cd = ClassDiagram('SmartGH')

cd.define_class("Vm")
cd.define_class("EC2", ['Vm'])
cd.define_class("EC2Free", ['Vm'])
cd.define_class('OpenStack', ['Vm'])
                
cd.define_class("Deployable")

cd.define_class("Web", ['Deployable'])
cd.define_class("FastWeb",['Web'])
cd.define_class("LowResWeb", ['Web'])

cd.define_class("Lb", ['Deployable'])
        
cd.define_class("Hopper", ['Deployable'])    
    
cd.define_class("CarHopper", ["Hopper"])
cd.define_class("SimplifiedHopper", ["Hopper"])
cd.define_class("FastHopper",["Hopper"])
cd.define_class("LowCostHopper",["Hopper"])

cd.define_class("FastCH", ["CarHopper", "FastHopper"])
cd.define_class("LowCostCH", ["CarHopper", "LowCostHopper"])
cd.define_class("NormalCH", ["CarHopper"])

cd.define_class("FullHopper", ["Hopper"])
cd.define_class("FastSH", ["SimplifiedHopper","FastHopper"])
cd.define_class("LowCostSH", ["SimplifiedHopper", "LowCostHopper"])

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

cd.define_attr_int('vmem', 'Vm', 1, 40)
cd.define_attr_int('rmem', 'Deployable', 0, 5)
cd.define_attr_int('port', 'Web', 8081, 8089)

smt = ModelSMT(cd)

smt.maxinst["Vm"] = 3
#smt.maxinst["FastCH"] = 1
smt.maxinst['Hopper'] = 8
#smt.maxinst["PaaSRedis"] = 2
smt.maxinst["Redis"] = 3
smt.maxinst["Web"] = 8
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
lb = smt.funcs['lb']
vmem = smt.funcs['vmem']
rmem = smt.funcs['rmem']
deploy = smt.funcs['deploy']

_t = lambda name: smt.types[name]
EC2 = smt.types['EC2']
EC2Free = smt.types['EC2Free']
OpenStack = smt.types['OpenStack']
BasicHopper = smt.types['FullHopper']
SimplifiedHopper = smt.types['SimplifiedHopper']
FastHopper = smt.types['FastHopper']
LowCostHopper = smt.types['LowCostHopper']
Hopper = smt.types['Hopper']
CarHopper = smt.types['CarHopper']
FastCH = smt.types['FastCH']
PaaSRedis = smt.types['PaaSRedis']
LocalRedis = smt.types['LocalRedis']
Web = smt.types['Web']
Sensor = smt.types['Sensor']
Pollution = smt.types['PollutionSensor']
Noise = smt.types['NoiseSensor']


typeof = smt.typeof
alive = smt.alive

_i = lambda name : smt.insts[name]
web = smt.insts['web00']
web1 = smt.insts['web01']
port = smt.funcs['port']
hopper00 = smt.insts['hopper00']
hopper01 = smt.insts['hopper01']
hopper02 = smt.insts['hopper02']
hopper03 = smt.insts['hopper03']



#shorthands end here


#auxiliary objects to display the result (painter), monitor change (cdriver), 
#and generate CloudML scripts

painter = ModelPainter(smt)

cdriver = ChangeDriver(smt)
cdriver.add_monitored('deploy', (x, rmem(x)*2))
cdriver.add_monitored('alive', (x, If(alive(x), 5, 10)))
cdriver.add_monitored('db', 2)
cdriver.add_monitored('sdb', 2)
cdriver.add_monitored('hp', 3)
cdriver.add_monitored('typeof', 20)

cloudml = CloudML(smt)
cloudml.attr = ['port']
cloudml.host = [('deploy', 'ubuntuReq', 'ubuntuPrv')]
cloudml.relation = [('db', 'redisReq', 'redisPrv'), ('sdb', 'redisReq', 'redisPrv'), ('hp', 'hopperReq', 'hopperPrv')]
cloudml.rev_relation = [('lb', 'lbReq', 'webPrv')]
cloudml.vm = ['Vm']
cloudml.internal = ['Deployable']
cloudml.external = ['PaaSRedis']

diversifyer = Diversifyer(smt, cdriver)
diversifyer.add_repo('Hopper')
diversifyer.add_repo('Sensor')
diversifyer.add_repo('Web')
diversifyer.add_repo('Vm')
#end of auxiliary

'''
' Create the main solver, and put the meta-model-related constraints
' into it
'''
solver = SoftSolverMsOpt()
for cst, comment in smt.hard_const:
        solver.add_hard(cst)



#At least one web by default    
#solver.add_soft(smt.alive(web), 1000)

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
# Two hoppers cannot be deployed on the same node
#solver.add_hard(smt.g_forall([(x,Hopper), (y, Hopper)], Implies(And([alive(x), alive(y), deploy(x)==deploy(y)]), x==y)))
# and two redis as well (because of the port)
#solver.add_hard(smt.g_forall([(x,LocalRedis), (y, LocalRedis)], Implies(And([alive(x), alive(y), deploy(x)==deploy(y)]), x==y)))
#each hopper should be covered by a web
exps = smt.g_ifalive_exists(x, Hopper, True, y, Web, hp(y)==x)
solver.add_hard(And(exps))
#Hoppers except Basic should have a sensor
#exp = And(smt.g_ifalive(x, FootHopper, smt.g_exist([(y, Sensor)], sdb(y) == db(x))))
#print '=======%s' % exp
#solver.add_hard(exp)
#solver.add_hard(And(smt.g_ifalive(x, CarHopper, smt.g_exist([(y, Sensor)], sdb(y) == db(x)))))

solver.add_hard(smt.g_ifalive(x, _t('LowCostSH'), rmem(x)==1))
solver.add_hard(smt.g_ifalive(x, _t('FastSH'), rmem(x)==2))
solver.add_hard(smt.g_ifalive(x, _t('LowCostCH'), rmem(x)==2))
solver.add_hard(smt.g_ifalive(x, _t('FastCH'), rmem(x)==3))
solver.add_hard(smt.g_ifalive(x, _t('NormalCH'), rmem(x)==5))
solver.add_hard(smt.g_ifalive(x, _t('FullHopper'), rmem(x)==6))

solver.add_hard(smt.g_ifalive(x, _t('Sensor'), rmem(x)==1))
solver.add_hard(smt.g_ifalive(x, _t('LocalRedis'), rmem(x)==2))
solver.add_hard(smt.g_ifalive(x, _t('Lb'), rmem(x)==1))

solver.add_hard(smt.g_ifalive(x, _t('EC2'), vmem(x)==8))
solver.add_hard(smt.g_ifalive(x, _t('EC2Free'), vmem(x)==4))
solver.add_hard(smt.g_ifalive(x, smt.types['OpenStack'], vmem(x)==32))


solver.add_hard(And(smt.g_ifalive(y, smt.types['Vm'], vmem(y) >= smt.g_sum(x, smt.types['Deployable'], rmem, deploy(x)==y))))

#eclusive sensor for FastCH
expr = smt.g_forall([(y, Sensor), (z, Sensor)], Implies(And(sdb(y)==db(x), sdb(z)==db(x)), y==z))
solver.add_hard(And(smt.g_ifalive(x, FastHopper, expr)))

theweb = Const('theweb', smt.CompInst)
solver.add_hard(smt.g_exist([(x, Web)], And(alive(x), x==theweb)))



cdriver.init_fixed_soft(solver)

for i in smt.insts.itervalues():
    if (not str(i).startswith('web00')) and str(i)!='null':
        solver.add_soft(Not(smt.alive(i)), 10)

(noise, pollution, fast, driving, walk, free, private, exfast, stable) = Bools(['noise','pollution', 'fast', 'driving', 'walk', 'free', 'private', 'exfast', 'stable'])
fsoft = lambda expr: cdriver.add_fixed_soft(expr, 300)

fsoft(Implies(noise, smt.g_exist([(x, _t('NoiseSensor'))], And([alive(sdb(x)), typeof(x)==_t('NoiseSensor'), sdb(x)==db(hp(theweb))])))) 
fsoft(Implies(pollution, smt.g_exist([(x, _t('PollutionSensor'))], And([alive(sdb(x)), typeof(x)==_t('PollutionSensor'), sdb(x)==db(hp(theweb))])))) 
fsoft(Implies(fast, smt.g_istypeof_x(hp(theweb), 'FastHopper')))
fsoft(Implies(driving, Or(smt.g_istypeof_x(hp(theweb), 'CarHopper'), typeof(hp(theweb))==_t('FullHopper'))))
fsoft(Implies(free, And(typeof(deploy(hp(theweb)))==_t('EC2Free'), typeof(deploy(theweb))==_t('EC2Free'))))
fsoft(Implies(walk, And(Not(smt.g_istypeof_x(hp(theweb), 'CarHopper')), typeof(theweb)==_t('LowResWeb'))))
fsoft(Implies(private, And(typeof(deploy(hp(theweb)))==_t('OpenStack'), typeof(deploy(db(hp(theweb))))==_t('OpenStack'))))
fsoft(Implies(exfast, And([fast, deploy(theweb)==deploy(hp(theweb)), Implies(alive(db(hp(theweb))), deploy(db(hp(theweb)))==deploy(theweb)) ])))

def prefered_type(cls):
    for cst in smt.g_prpg(x, _t(cls), Implies(alive(x), typeof(x)==_t(cls))):
        cdriver.add_fixed_soft(cst, 1)
        solver.add_soft(cst,1)

prefered_type('LowCostSH')
prefered_type('EC2Free')
prefered_type('FastWeb')
prefered_type('NoiseSensor')
prefered_type('PaaSRedis')

do_search(solver)

painter.eval = solver.model().eval

print solver.get_broken()
print solver.get_broken_weight()
cloudml.meval = solver.model().eval
painter.make_graph()



resfile = open('result', 'w')
abstypes = ['hopper', 'hopper', 'sensor']
contexts = [
            [noise], [pollution], [fast], [driving], [walk], [free], [private], [exfast],
            [noise, fast], [noise, driving], [pollution, walk], [pollution, free], [noise, private], [noise, exfast], [noise, stable],
            [noise, fast, private], [noise, walk, free], [noise, driving, free], [pollution, walk, stable], [pollution, driving, private],
            [driving, fast, free], [driving, exfast],  [walk, exfast, stable]
           ]

init_meval = solver.model().eval
def grow(solver, wakeup, wakeup_type, onlyhopper=False):
    avail_types = { 
                   'hopper' : ['FastCH', 'LowCostCH', 'NormalCH', 'LowCostSH', 'FastSH', 'FullHopper'],
                   'web' : ['FastWeb', 'LowResWeb'],
                   'vm' : ['EC2', 'EC2Free', 'OpenStack'],
                   'sensor' : ['NoiseSensor', 'PollutionSensor'],
                   'redis' : ['PaaSRedis', 'LocalRedis']
                   }
    cdriver.start_over_meval(solver, init_meval)
    if onlyhopper:
        towakeup = random.sample([item for item in smt.insts.itervalues() if str(item).startswith('hopper')], wakeup)
    else:
        towakeup = random.sample([item for item in smt.insts.itervalues() if str(item)!='null' and not str(item).startswith('lb')], wakeup)
    for inst in towakeup:
        solver.add_soft(smt.alive(inst), 300)
        if wakeup_type>0:
            solver.add_soft(smt.typeof(inst)==_t(random.choice(avail_types[str(inst)[:-2]])), 300)
            wakeup_type -= 1
    #print solver.soft
    print 'growing...'
    do_search(solver)
    #print solver.get_broken()
    
#grow(solver, 12, 12)
#painter.eval=solver.model().eval
#painter.make_graph()
#
#quit()

try:
    for i in range(2, 33):
        for j in range(0, i+1):
            print "------------------%d:%d----------------------"%(i,j)
            real_i = i
            try:
                if i > 25 and j <= i-25:
                    real_i = i-25
                    grow(solver, i-25, j, True)
                elif i < 25:
                    grow(solver, i, j, False)
                else:
                    continue
            except:
                continue
            
            resfile = open('result', 'a')
            meval = solver.model().eval
            #painter.eval = meval
            (size, shannon) = painter._shannon_without_show(solver.model().eval)
            resfile.write('%d,%d,%s,%.4f,'%(real_i,j, size, shannon));
            #painter.make_graph()
            costs = []
            for ctx in contexts:
                print ctx
                cdriver.start_over_meval(solver, meval)
                
                for predicate in ctx:
                    solver.add_soft(predicate, 100)
                do_search(solver)
                cost = solver.get_broken_weight()
                resfile.write("%i,"%cost)
                costs.append(cost)
                print 'Total cost: %d, %s' %(solver.get_broken_weight(),solver.get_broken())
                #painter.eval = solver.model().eval
                #painter.make_graph()
            resfile.write("%.4f\n"%(sum(costs)*1.0 / len(costs)))
            
            resfile.close()
finally:
    resfile.close()


quit()


for i in range(0,100):
    #try:
        cdriver.start_over(solver)
        command = console_input()
        if command == 'quit':
            quit()
        elif command == 'diversify grow':
            #for n in range(0,3):
            diversifyer.diversify_grow_run(solver)
        elif command == 'simple grow':
            diversifyer.simple_grow_run(solver, solver.model().eval, 'hopper', 4)            
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
        #print cloudml.generate_instances()
        #print solver.soft
        print 'Total cost: %d, %s' %(solver.get_broken_weight(),solver.get_broken())
        #print meval()
        print 'the web is %s' % (web for web in smt.insts if web==theweb)
        painter.make_graph()
    #except:
        s = str(sys.exc_info())
        print "Unexpected error:%s" % s
        if 'on closed file' in s:
            quit()










