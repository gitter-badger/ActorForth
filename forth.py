# Re-implementing an inferred stack language, with unification of type
# variables in Python

# Program syntax
def Done():
    return 'Done'

def Continue():
    return 'Continue'

def LitI(i,p):
    return ["LitI", i, p]

def LitB(i,p):
    return ["LitB", i, p]

def Cmd(s,p):
    return ["Cmd", s, p]

def Func(p1,p2):
    return ["Func", p1, p2]


# Type syntax
# Saturated type (Int, Bool, etc.)
def T(s):
    return ["T",s]

# Stack with head and tail
def Stack(t1,t2):
    return [":-",t1,t2]

# Function type
def TArr(t1,t2):
    return [":->",t1,t2]

# Type variable
def TV(s):
    return ["TV", s]

# Bottom of stack
def Bot():
    return 'Bot'

# Gensym counter and dictionary of constraints.
i = 0
cs = []

# Gensym
def gensym():
    global i, cs
    res = 't{}'.format(i)
    i += 1
    return res

def stackError(f,s):
    raise ValueError("incorrect argument to {} {}".format(f,s))

# Generate a new type variable
def newTV():
    s = gensym()
    return ['TV', s]


def lookup(x,l):
    return l[[v[0] for v in l].index(x)][1]

# Gather the constraints on a program
# gather :: [(String, Type)] -> Pgrm -> Gather Type
def gather(gamma,pgrm):
    global cs, i
    if pgrm == Done():
        return Bot()
    elif pgrm == Continue():
        return(lookup("s",gamma))
    elif pgrm[0] == "LitI":
        [_,i,p] = pgrm
        return gatherLit("Int",gamma,p)
    elif pgrm[0] == "LitB":
        [_,i,p] = pgrm
        return gatherLit("Bool",gamma,p)
    elif pgrm[0] == "Cmd":
        [_,s,p] = pgrm
        # Lookup the function type.
        tf = lookup(s,gamma)
        # Get all the free type variables from the function type.
        fv = freeVars(tf)
        # Rename all free variables in the function type.
        tf = rename(tf,fv)
        # Gather constraints for the rest of the program.
        a = gather(gamma,p)
        b = newTV()
        # Add a constraint, the function type must take a to b.
        cs = [(tf, TArr(a,b))] + cs
        # The whole command returns something of type b.
        return b

# Literal cases
def gatherLit(t,gamma,p):
    global cs,i
    # Gather constraints for the rest of the program.
    s = gather(gamma,p)
    tl = newTV()
    # The result type.
    res = Stack(T(t),s)
    cs = [(tl, res)] + cs
    return res

# Get all free type variables in a type.
# freeVars :: Type -> Set String
def freeVars(t):
    return(f(t,set()))

def f(t,l):
    if t == Bot():
        return l
    elif t[0] == "TV":
        [_,s] = t
        l.add(s)
        return l
    elif t[0] == ":->":
        [_,a,b] = t
        return f(b,(f(a,l)))
    elif t[0] == ":-":
        [_,a,b] = t
        return f(b,(f(a,l)))
    else:
        return l

def rename(t,s):
    acc = {}
    for i in s:
        acc[i] = newTV()
    for i,j in acc.items():
        t = sub(i,j,t)
    return t

# Substitute type variable x for t in y
# In math notation, sub (x, t, y) = y[t/x]
def sub(x,t,y):
    if y == Bot():
        return y
    elif y[0] == "T":
        return y
    elif y[0] == "TV":
        [_,xp] = y
        if x == xp:
            return t
        else:
            return y
    elif y[0] == ":-":
        [_,a,b] = y
        return [":-", sub(x,t,a), sub(x,t,b)]
    elif y[0] == ":->":
        [_,a,b] = y
        return [":->", sub(x,t,a), sub(x,t,b)]
    else:
        raise ValueError("Bad type {}".format(y))


# Unify a list of constraints
# unify :: [(Type, Type)] -> [(String, Type)] -> [(String, Type)]
def unify(tps,s):
    if tps == []:
        return s # get >>= pure
    else:
        (l,r) = tps[0]
        
        print("\nUnifying\n{}\n{}".format(l,r))
        print("Solutions:{}".format(s))
        print("List:{}\n".format(tps))
        rest = tps[1:]
        if l[0] == r[0] == ":-":
            [_,tx,ty] = l
            [_,ux,uy] = r
            rest = [(tx,ux),(ty,uy)] + rest
            return unify(rest,s)
        elif l[0] == r[0] == ":->":
            [_,tx,ty] = l
            [_,ux,uy] = r
            rest = [(tx,ux),(ty,uy)] + rest
            return unify(rest,s)
        elif l[0] == r[0] == "T":
            if l[1] == r[1]:
                return unify(rest,s)
            else:
                raise ValueError("Failed to unify {} and {}".format(l[1], r[1]))
        elif l[0] == "TV" and r[0] == "TV":
            if l[1] == r[1]:
                return unify(rest,s)
        elif l[0] == "TV":
            [_,x] = l
            t = r
            if occurs(x,t):
                raise ValueError("Cannot construct the infinite type {} ~ {}".format(x,t))
            else:
                s = [(x,t)] + s
                w = [(sub(x,t,v[0]),sub(x,t,v[1])) for v in rest]
                return(unify(w,s))
        elif r[0] == "TV":
            w = [(r,l)] + rest
            return(unify(w,s))
        else:
            raise ValueError("Unification failed {}".format(tps))

# Occurs check
def occurs(x,t):
    if t == Bot():
        return False
    elif t[0] == ":-":
        [_,a,b] = t
        return occurs(x,a) or occurs(x,b)
    elif t[0] == ":->":
        [_,a,b] = t
        return occurs(x,a) or occurs(x,b)
    elif t[0] == "TV":
        return x == t[1] 

def solve(gamma,x):
    global cs,i
    i = 0
    cs = []
    # ty is the type to solve for
    ty = gather(gamma,x)
    # res contains the solved constraints
    res = unify(cs,[])
    print("Unification result: {}".format(res))
    for i,j in res:
        ty = sub(i,j,ty)
    return ty
    

dupType = TArr(Stack(TV("a"),TV("s")),Stack(TV("a"),Stack(TV("a"),TV("s"))))
addType = TArr(Stack(T("Int"),Stack(T("Int"),TV("s"))),
               Stack(T("Int"),TV("s")))
dropType = TArr(Stack(TV("a"),TV("s")),TV("s"))

stdEnv = [("dup", dupType), ("add",addType),("drop",dropType)]

# print("Lookup: {}".format(lookup("add", stdEnv)))
# print(TArr(Stack(TV("a"),TV("s")),Stack(TV("a"),Stack(TV("a"),TV("s")))))
# print("freeVars(dupType): ", freeVars(dupType))
# print("Rename: ", rename(dupType,freeVars(dupType)))

# print("Gather: ", gather(stdEnv,Cmd("dup",LitI(5,Done()))))
# print("Gather: ", gather(stdEnv,Cmd("dup",LitI(3,Done()))))
# print("Gather: ", gather(stdEnv,Cmd("add", LitI(5,LitI(3,Done())))))

# print("Constraints after gathering:")
# for i in cs:
#     print(i)

ex1 = Cmd("add",LitI(5,LitI(3,Done())))
ex2 = Cmd("dup",LitI(5,Done()))
print("Final result: ", solve(stdEnv,ex2))
