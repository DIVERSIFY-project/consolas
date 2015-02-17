'''
Created on 17 Feb 2015

@author: Hui Song
'''

class CloudML:


    def __init__(self, smt):
        self.smt = smt
        self.cd = smt.cd
        self.attr = []
        self.host = []
        self.relation = []
        self.rev_relation = []
        self.vm = []
        self.internal = []
        self.external = []    
        self.meval = None 
        
    def generate_instances(self):
        meval = self.meval
        lines = []
        smt = self.smt
        for inst in smt.insts:
            xinst = smt.insts[inst]
            if str(meval(smt.alive(xinst)))=='False':
                continue
            type = str(meval(smt.typeof(xinst)))
            line = '%s %s typed %s' % (self.get_category(type), inst, type)
            properties = []
            for attr in self.attr:
                xattr = self.smt.funcs[attr]
                if type in self.cd.attr[attr]:
                    properties.append('(%s : %s)' % (attr, meval(xattr(xinst))))
            if len(properties)!=0:
                line = '%s { properties: %s}' %(line, ", ".join(properties))
            lines.append(line)
         
        for host, fromport, toport in self.host:
            xhost = self.smt.funcs[host]
            for inst in smt.insts:
                xinst = smt.insts[inst]
                if str(meval(smt.alive(xinst)))=='False':
                    continue
                target = meval(xhost(xinst))
                if str(meval(smt.alive(target)))=='False':
                    continue
                lines.append('host %s.%s on %s.%s' % (inst, fromport, target, toport))
        
        for rel, fromport, toport in self.relation + self.rev_relation:
            xrel = self.smt.funcs[rel]
            for inst in smt.insts:
                xinst = smt.insts[inst]
                if str(meval(smt.alive(xinst)))=='False':
                    continue
                target = meval(xrel(xinst))
                if str(meval(smt.alive(target)))=='False':
                    continue
                if (rel, fromport, toport) in self.rev_relation:
                    first, second = (target, xinst)
                else:
                    first, second = (xinst, target)
                ftype = meval(smt.typeof(first))
                stype = meval(smt.typeof(second))
                lines.append('connect %s.%s to %s.%s typed %s2%s' % (first, fromport, second, toport, ftype, stype))
                    
                
        return 'instances{ \n%s\n}' % '\n'.join('\t'+line for line in lines)        
            
    def get_category(self, type):
        supertypes = self.smt.indirect_super_class[type] | set([type])
        if set(self.vm) & supertypes :
            return 'vm'
        elif set(self.internal) & supertypes:
            return 'internal component'
        elif set(self.external) & supertypes:
            return 'external component'
        else:
            return None