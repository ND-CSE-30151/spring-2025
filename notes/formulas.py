class Formula(object):
    def __init__(self, op, args):
        if op not in ["var", "and", "or", "not"]:
            raise ValueError()
        self.op = op
        self.args = args
        
    def __str__(self):
        if self.op == "var":
            return self.args[0]
        elif self.op == "not":
            x, = self.args
            if x.op in ["and", "or"]:
                x = f"({x})"
            return f"¬{x}"
        elif self.op == "and":
            arg_strs = []
            for arg in self.args:
                if arg.op == "or":
                    arg_strs.append(f"({arg})")
                else:
                    arg_strs.append(str(arg))
            return " ∧ ".join(arg_strs)
        elif self.op == "or":
            return " ∨ ".join(map(str, self.args))
        else:
            raise ValueError()
        
    def pretty(self, limit=5):
        if self.op == "var":
            return self.args[0]
        elif self.op == "not":
            x, = self.args
            if x.op in ["and", "or"]:
                x = "({})".format(x.pretty(limit))
            else:
                x = x.pretty()
            return "¬{}".format(x)
        elif self.op == "and":
            arg_strs = []
            for arg in self.args[:limit]:
                if arg.op == "or":
                    arg_strs.append(f"({arg.pretty()})")
                else:
                    arg_strs.append(arg.pretty())
            if len(self.args) > limit:
                arg_strs.append("...")
            return " ∧ ".join(arg_strs)
        elif self.op == "or":
            arg_strs = [arg.pretty() for arg in self.args[:limit]]
            if len(self.args) > limit:
                arg_strs.append("...")
            return " ∨ ".join(arg_strs)
        else:
            raise ValueError()

    def __and__(self, other):
        return conjoin(self, other)
    def __rand__(self, other):
        return conjoin(other, self)
    def __or__(self, other):
        return disjoin(self, other)
    def __ror__(self, other):
        return disjoin(other, self)
    def __invert__(self):
        return Formula("not", [self])

    def size(self):
        """Number of nodes in the formula as an AST."""
        if self.op == "var":
            return 1
        else:
            return sum(arg.size() for arg in self.args) + 1
        
    def vars(self):
        if self.op == "var":
            return set([self.args[0]])
        else:
            return set.union(*[arg.vars() for arg in self.args])

    def evaluate(self, asst):
        if self.op == "var":
            return asst[self.args[0]]
        elif self.op == "and":
            return all(arg.evaluate(asst) for arg in self.args)
        elif self.op == "or":
            return any(arg.evaluate(asst) for arg in self.args)
        elif self.op == "not":
            return not self.args[0].evaluate(asst)
        else:
            raise ValueError()

    def satisfying_assignment(self):
        import itertools
        vars = list(self.vars())
        for vals in itertools.product([False, True], repeat=len(vars)):
            asst = dict(zip(vars, vals))
            if self.evaluate(asst):
                return asst
        return None

    def satisfiable(self):
        return self.satisfying_assignment() is not None

def disjoin(*args):
    new_args = []
    for arg in args:
        if arg == True: return True
        elif arg == False: continue
        elif arg.op == "or": new_args.extend(arg.args)
        else: new_args.append(arg)
    return Formula("or", new_args)

def conjoin(*args):
    new_args = []
    for arg in args:
        if arg == True: continue
        elif arg == False: return False
        elif arg.op == "and": new_args.extend(arg.args)
        else: new_args.append(arg)
    return Formula("and", new_args)

def var(x):
    return Formula("var", [x])
