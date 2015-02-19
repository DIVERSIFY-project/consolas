'''
Created on Feb 19, 2015

@author: Hui Song
'''
def do_search(solver):
    solver.init_solver()
    
    print "start searching"        
    (result, time) = solver.search_with_timing()
    print '%s: %.4f'%(result,time)
    
def console_input(monitor = None):
    result = []
    for j in range(0,100):
        perm = False
        s = raw_input('(constraint [!] [ | weight ]) | go | quit>>')
        if s == 'quit' or s == 'q':
            quit()
        if s == 'go':
            break
        if '|' in s:
            conswei = s.split('|')            
        else:
            conswei = [s, '1000']
        csttext = conswei[0].strip()
        if csttext.endswith('!'):
            perm = True
            conswei[0] = csttext[:-1].strip()
        print conswei
        result.append((conswei[0], int(conswei[1].strip()), perm))
    print result
    return result