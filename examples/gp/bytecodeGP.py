import copy
import random
import re
import sys
import warnings
import operator, math

import dis
import opcode
import types
import inspect
import importlib

from deap import base,creator,gp

class PrimitiveTree(bytearray):
    """Tree spefically formated for optimization of genetic
    programming operations.
    """
    co_names = tuple()
    co_vars  = tuple()
    funcWrapperCode = bytes([ dis.opmap['LOAD_CONST'], 0, 0,
                    dis.opmap['LOAD_CONST'], 1, 0,
                    dis.opmap['MAKE_FUNCTION'], 0, 0,
                    dis.opmap['RETURN_VALUE']
                    ])

    def __init__(self, content):
        if isinstance(content, bytearray):
            bytearray.__init__(self, content)
            return

        if len(self.co_names) == 0:
            PrimitiveTree.co_names = tuple(self.pset.context.keys())        # Pareil pour tous les PrimitiveTree
            PrimitiveTree.co_vars = tuple(chr(a) for a in range(120, 120+len(self.pset.ins)))

        self.extend(self._convertToBytecode(content))
        self.append(dis.opmap['RETURN_VALUE'])             # On ajoute le return final

        self.size = len(content)            # Plus rapide, mais seulement possible a l'initialisation
    
    def _convertToBytecode(self, content):
        arities = []
        num_args = []
        b = bytearray()

        for node in content:
            if node.arity == 0:
                # Terminal
                if isinstance(node, gp.Ephemeral):
                    raise NotImplementedError
                else:
                    # Arguments are named ARGx ou x va de 0 a ...
                    argnbr = int(node.name[3:])
                    b.extend([dis.opmap['LOAD_FAST'], argnbr, 0]) # Supporte UNIQUEMENT un seul argument pour l'instant   


                if len(arities) == 0:
                    assert len(content) == 1
                    break   # Si on n'avait qu'un seul noeud  

                # Si on a ajoute un terminal, c'est qu'on vient de terminer une branche.
                # On soustrait l'arity de notre parent

                arities[-1] -= 1
                while arities[-1] == 0:
                    b.extend([dis.opmap['CALL_FUNCTION'], num_args[-1], 0]) # On suppose qu'il n'y a pas de kwargs       
                    arities.pop()
                    num_args.pop()

                    if len(arities) == 0:
                        break
                    arities[-1] -= 1
            else:
                symbolPos = self.co_names.index(node.name)
                arities.append(node.arity)            # On se rappelle de notre arity pour savoir quand ecrire le CALL
                num_args.append(node.arity)

                # On suppose qu'on n'a pas plus de 255 symboles externes
                # Sinon il faudrait mettre le MSD comme dernier argument
                b.extend([dis.opmap['LOAD_GLOBAL'], symbolPos, 0])

        return b

    @classmethod
    def compile(cls, expr, pset):
        code = types.CodeType(
            len(cls.co_vars),           # argcount
            0,                          # kwonlyargcount
            len(cls.co_vars),           # nlocals
            200,                        # stacksize      # Temporaire
            67,                         # flags           # Hum...
            bytes(expr),                # codestring
            (),                         # consts
            cls.co_names,               # names
            cls.co_vars,                # varnames
            "DEAP-Bytecode-Compiler",   # filename
            "Prim",                     # name
            1,                          # firstlineno
            bytes([1,1]),               # lnotab
            (),                         # freevars
            ()                          # cellvars
        )

        funcCode = types.CodeType(
            0,                          # argcount
            0,                          # kwonlyargcount
            0,                          # nlocals
            5,                          # stacksize      # Temporaire
            67,                         # flags=67           # Hum...
            cls.funcWrapperCode,        # codestring
            (code, 'Prim'),             # consts=()
            (),                         # names=self.co_names
            (),                         # varnames=('x',)
            "DEAP-Bytecode-Compiler",   # filename="DEAP-Bytecode-Compiler"
            "Func",                     # name="Prim"
            1,                          # firstlineno=1
            bytes([1,1]),               # lnotab=bytes([1,1])
            (),                         # freevars=()
            ()                          # cellvars=()
        )

        #self.func = types.FunctionType(code, self.pset.context)
        #return self.func

        return eval(funcCode, pset.context, {})

        
    def __deepcopy__(self, memo):
        """ Faster deepcopy """
        new = self.__class__(self)
        new.__dict__.update(copy.deepcopy(self.__dict__, memo))
        return new

    def __getitem__(self, key):
        if isinstance(key, slice):
            return bytearray.__getitem__(self, key)

        else:   # Int
            currentPos = 0
            i = -3
            while currentPos <= key:
                i += 3
                if bytearray.__getitem__(self, i) in (dis.opmap['LOAD_GLOBAL'], dis.opmap['LOAD_FAST']):
                    currentPos += 1

            if bytearray.__getitem__(self, i) == dis.opmap['LOAD_GLOBAL']:
                return self.pset.mapping[self.co_names[bytearray.__getitem__(self, i+1)]]
            else:   # Terminal
                return list(self.pset.terminals.values())[0][0]     # TODO Ok, a travailler, faut pas renvoyer n'importe quel terminal random...


    def __setitem__(self, key, val):
        if isinstance(val, bytearray):
            # Mise a jour de la taille
            self.size += len([1 for b in val if b in (dis.opmap['CALL_FUNCTION'], dis.opmap['LOAD_FAST'])]) - \
                            len([1 for b in bytearray.__getitem__(self, key) if b in (dis.opmap['CALL_FUNCTION'], dis.opmap['LOAD_FAST'])])
            bytearray.__setitem__(self, key, val)
        else:
            # On suppose que c'est une expression a transformer en bytecode (utile pour les mutations)
            # Pas certain que ca fonctionne pour mutNodeReplacement par contre...
            b = self._convertToBytecode(val)
            self.size += len(val) - len([1 for b in bytearray.__getitem__(self, key) if b in (dis.opmap['CALL_FUNCTION'], dis.opmap['LOAD_FAST'])])
            bytearray.__setitem__(self, key, b)

    def __str__(self):
        # Excessivement mal fait et peu optimise
        s = ""
        for i,b in enumerate(self[::3]):
            if b == dis.opmap['LOAD_GLOBAL']:
                if len(s) > 1 and s[-1] != "(" and s[-2] != ",":
                    s += ", " + self.co_names[bytearray.__getitem__(self, 3*i+1)]+"("
                else:
                    s += self.co_names[bytearray.__getitem__(self, 3*i+1)]+"("
            elif b == dis.opmap['CALL_FUNCTION']:
                s += ")"
            elif b == dis.opmap['LOAD_FAST']:
                if len(s) > 1 and s[-1] != "(" and s[-2] != ",":            
                    s += ", x"
                else:
                    s += "x"
        return s

    def __len__(self):
        return self.size

    @property
    def height(self):
        current_depth = 0
        max_depth = 0
        for b in self[::3]:
            if b == dis.opmap['LOAD_GLOBAL']:
                current_depth += 1
            elif b == dis.opmap['CALL_FUNCTION']:
                current_depth -= 1
            elif b == dis.opmap['LOAD_FAST']:
                max_depth = max(max_depth, current_depth+1)
        return max_depth - 1

    @property
    def root(self):
        return self[0]

    def searchSubtree(self, begin):
        currentPos = 0
        i = -3
        while currentPos <= begin:
            i += 3
            if bytearray.__getitem__(self, i) in (dis.opmap['LOAD_GLOBAL'], dis.opmap['LOAD_FAST']):
                currentPos += 1
        realBegin = i

        end = realBegin+3

        if bytearray.__getitem__(self, realBegin) != dis.opmap['LOAD_FAST']:  # Pas un terminal
            callOpToSee = 1
            while callOpToSee > 0:
                if bytearray.__getitem__(self, end) == dis.opmap['CALL_FUNCTION']:
                    callOpToSee -= 1
                elif bytearray.__getitem__(self, end) == dis.opmap['LOAD_GLOBAL']:
                    callOpToSee += 1
                end += 3

        return slice(realBegin, end)

        

if __name__ == '__main__':
    random.seed()

    expr = gp.genGrow(pset, 3, 4)
    print([p.name for p in expr])
    print("\n")

    creator.create("FitnessMin", base.Fitness, weights=(-1.0,))
    creator.create("Individual", PrimitiveTree, fitness=creator.FitnessMin, pset=pset)

    p = creator.Individual(expr)

    q = copy.deepcopy(p)
    func = q.compile()
    d = dis.Bytecode(q.code)
    print(d.dis())

    print(func(3))
    print(len(q), len(expr))

    
