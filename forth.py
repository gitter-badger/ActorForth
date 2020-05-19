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


# Type
def T(s):
    return ["T",s]

def Stack(t1,t2):
    return [":-",t1,t2]

def TArr(t1,t2):
    return [":->",t1,t2]

def TV(s):
    return ["TV", s]

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

ex1 = Cmd("add",LitI(5,LitI(3,Done())))

def lookup(x,l):
    return l[[v[0] for v in l].index(x)][1]

# print(ex1)
# print(Cmd("add",LitI(5,Done())))
# gather :: Set (String, Type) -> Pgrm -> Gather Type
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
        tf = lookup(s,gamma)
        fv = freeVars(tf)
        tf = rename(tf,fv)
        a = gather(gamma,p)
        b = newTV()
        cs = [(tf, TArr(a,b))] + cs
        return b

def gatherLit(t,gamma,p):
    global cs,i
    s = gather(gamma,p)
    tl = newTV()
    res = Stack(T(t),s)
    cs = [(tl, res)] + cs
    return res

# Get all free type variables in a type.
# freeVars :: Type -> [String]
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
        raise ValueError("Incorrect type {}".format(t))

def rename(t,s):
    acc = {}
    for i in s:
        acc[i] = newTV()
    for i,j in acc.items():
        t = sub(i,j,t)
        # print(t)
    return t

def sub(x,t,y):
    if y == Bot():
        return y
    elif y[0] == "TV":
        [_,n] = y
        if x == n:
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


print(gensym())
print(newTV())
dupType = TArr(Stack(TV("a"),TV("s")),Stack(TV("a"),Stack(TV("a"),TV("s"))))
print(TArr(Stack(TV("a"),TV("s")),Stack(TV("a"),Stack(TV("a"),TV("s")))))
print("freeVars(dupType): ", freeVars(dupType))
print("Rename: ", rename(dupType,freeVars(dupType)))
# print("Gather: ", gather([("dup", dupType)],Cmd("dup",LitI(3,Done()))))
gather([("dup", dupType)],LitI(3,Done()))
print("Constraints after gathering: ", cs)

