#encoding: utf8
# Pedro Bastos
# 93150


from semantic_network import *
from bayes_net import *
from constraintsearch import *
from collections import Counter


class MyBN(BayesNet):

    def individual_probabilities(self):
        # probabilities dic
        probs = dict()

        # for each dependency
        for x in self.dependencies.keys():
            # get prob
            probs[x] = sum([self.jointProb([(x, True)]+ conj) for conj in self.conjs([i for i in self.dependencies.keys() if i != x])])
        return probs

    def conjs(self, dep_vars):
        if len(dep_vars) != 1:
            lst = []
            [lst.append([(dep_vars[0], True)] + conj) for conj in self.conjs(dep_vars[1:])]
            [lst.append([(dep_vars[0], False)] + conj) for conj in self.conjs(dep_vars[1:])]

            return lst
        
        return [[(dep_vars[0],True)], [(dep_vars[0],False)]]




class MySemNet(SemanticNetwork):
    def __init__(self):
        SemanticNetwork.__init__(self)

    def translate_ontology(self):
        # sorted dictionary
        sorted_dic = dict()
        # original dictionary
        dic = dict()
        # returning list
        lst = []

        # subtypes
        query_result = self.query_local(relname="subtype")

        # append relations
        for x in query_result:
            if x.relation.entity2 not in dic.keys():
                dic[x.relation.entity2] = [x.relation.entity1]
            else:
                dic[x.relation.entity2].append(x.relation.entity1)
        
        # sort dict
        for x in sorted(dic.keys()):
            sorted_dic[x] = dic.get(x)

        # append strings to list
        for x in sorted_dic.keys():
            # subtypes
            string = ''
            unique_list = sorted((list(set(sorted_dic.get(x)))))
            # append to string
            for k in unique_list:
                if k != unique_list[-1]:
                    string += str(k).capitalize() + '(x) or '
                else:
                    string += str(k).capitalize() + '(x) '

            # append fully formatted string to list
            lst.append('Qx ' + string + '=> ' + str(x).capitalize() + '(x)')

        return lst

    def query_inherit(self, entity, assoc):
        # all queries
        all_queries = []

        # entity associations
        [all_queries.append(x) for x in self.declarations if x.relation.name == assoc and  x.user == entity] 

        # inherited queries
        query_result = self.query_local()
        for x in query_result:
            # if is predecessor
            if self.predecessor(x.relation.entity2, entity):
                # get predecessor associations with assoc name and append
                q1 = self.query_local(e1=x.relation.entity2, relname=assoc)
                [all_queries.append(q) for q in q1 if isinstance(q.relation, Association) and q not in all_queries]
        
        # inverse queries
        inv_query = self.query_local(e2=entity)
        [all_queries.append(x) for x in inv_query if isinstance(x.relation, Association) and x.relation.inverse == assoc]
                    
        return all_queries

    def query(self, entity, relname):
        # all queries
        all_queries = []

        # if relation is a subtype
        if relname == 'subtype':
            return [dec.relation.entity2 for dec in self.declarations if dec.relation.entity1 == entity and isinstance(dec.relation, Subtype)]

        # if relation is a member
        if relname == 'member':
            return [dec.relation.entity2 for dec in self.declarations if dec.relation.entity1 == entity and isinstance(dec.relation, Member)]

        # else handle the associations
        else:
            # get association properties
            triple_list = [dec.relation.assoc_properties() for dec in self.declarations if dec.relation.name == relname]
            # get the most common one
            triple = Counter(triple_list).most_common(1)[0][0]
            
            # get inherit associations
            recursive = self.query_2(entity, relname, triple[0])

            for x in recursive:
                # avoid repeats
                if x.relation.entity2 not in all_queries:
                    # if not association
                    if not isinstance(x.relation, Association):
                        all_queries.append(x.relation.entity2)
                    else:
                        # if association properties match the most common
                        if x.relation.assoc_properties() == triple:
                            all_queries.append(x.relation.entity2)
                        
            return all_queries

    def query_2(self, entity, relname, card):
        # predecessors
        predecessors = [ self.query_2(dec.relation.entity2, relname, card) for dec in self.declarations if isinstance(dec.relation, (Member,Subtype)) and dec.relation.entity1 == entity]
        predecessors = [ dec for lst in predecessors for dec in lst]
        # local associations
        ent_local = self.query_local(e1=entity, relname=relname)

        # if is multiple, inherit counts
        if card == 'multiple' or card == None:
            return ent_local + predecessors
        # if is single, return only the most common
        else:
            if len(ent_local) > 0:
                return [Counter(ent_local).most_common(1)[0][0]]
            elif len(predecessors) > 0:
                return [Counter(predecessors).most_common(1)[0][0]]

        return []

    def predecessor(self, sub_ent, ent):
        # get predecessors
        predec = [dec.relation.entity2 for dec in self.declarations if dec.relation.entity1 == ent and isinstance(dec.relation, (Member,Subtype))]
        # compare
        return sub_ent in predec or any([self.predecessor(sub_ent, pre) for pre in predec])

class MyCS(ConstraintSearch):
    
    def search_all(self,domains=None):

        if domains==None:
            domains = self.domains

        # se alguma variavel tiver lista de valores vazia, falha
        if any([lv==[] for lv in domains.values()]):
            return []

        # se nenhuma variavel tiver mais do que um valor possivel, sucesso
        if all([len(lv)==1 for lv in list(domains.values())]):
            return [{ v:lv[0] for (v,lv) in domains.items() }]

        # all solutions array
        all_sols = []

        # continuação da pesquisa
        for var in domains.keys():
            if len(domains[var])>1:
                for val in domains[var]:
                    newdomains = dict(domains)
                    newdomains[var] = [val]
                    edges = [(v1,v2) for (v1,v2) in self.constraints if v2==var]
                    newdomains = self.constraint_propagation(newdomains,edges)
                    # recursive
                    s = self.search_all(newdomains)
                    if s != []:
                        # concatenate solution
                        all_sols += s

                return all_sols


