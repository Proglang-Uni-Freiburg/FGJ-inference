import FGJ_AST as FGJ
import FGJ_GT_AST as FGJ_GT
import FGJ_auxiliary_typing as AUX

from typing import Generator, Any
from frozenlist import FrozenList
from itertools import product


def fresh(name: str) -> Generator[FGJ_GT.TypeVarA, Any, None]:
    count = 0
    while True:
        yield FGJ_GT.TypeVarA(name + str(count))
        count += 1


def is_solved_form(C: set[FGJ_GT.sc]) -> bool:
    lst: list[str] = list()
    for constraint in C:
        match constraint:
            case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(_), FGJ_GT.TypeVarA(_)):
                pass
            case FGJ_GT.EqualC(FGJ_GT.TypeVarA(_), FGJ_GT.TypeVarA(_)):
                pass
            case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(_)) if a not in lst:
                lst.append(a)
            case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(_)) if a not in lst and not occoursIn(FGJ_GT.TypeVarA(a), constraint.t2):
                lst.append(a)
            case _:
                return False
    return True


def gen_C_prime(C: FGJ_GT.C) -> Generator[set[FGJ_GT.sc], Any, Any]:
    sc_set: set[FGJ_GT.sc] = set()
    oc_list: list[FGJ_GT.oc] = list()
    for c in C:
        match c:
            case FGJ_GT.SubTypeC():
                sc_set.add(c)
            case FGJ_GT.EqualC():
                sc_set.add(c)
            case _:
                oc_list += [c]

    for comb in product(*oc_list):
        out = sc_set.copy()
        for lst in comb:
            for elem in lst:
                out.add(elem)
        yield out


def subOne(y: FGJ.TypeVar, a: FGJ_GT.TypeVarA, t: FGJ.Type) -> FGJ.Type:
    match t:
        case FGJ_GT.TypeVarA(a.name):
            return y
        case FGJ.TypeVar(_):
            return t
        case FGJ.NonTypeVar(n, ts):
            return FGJ.NonTypeVar(n, FrozenList([subOne(y, a, ti) for ti in ts]))
        case _:
            raise Exception("CANT GO HERE - BUT TYPECHECKER")


def sub(ys: list[FGJ.TypeVar], ass: list[FGJ_GT.TypeVarA], t: FGJ.Type) -> FGJ.Type:
    for yi, ai in zip(ys, ass):
        t = subOne(yi, ai, t)
    return t


def subConstraint(t: FGJ.Type, a: FGJ_GT.TypeVarA, C: set[FGJ_GT.sc]) -> set[FGJ_GT.sc]:
    newC = C.copy()
    for constraint in C:
        match constraint:
            case FGJ_GT.EqualC(t1, t2):
                newC.remove(constraint)
                newC.add(FGJ_GT.EqualC(subSingle(t, t1, a), subSingle(t, t2, a)))
            case FGJ_GT.SubTypeC(t1, t2):
                newC.remove(constraint)
                newC.add(FGJ_GT.SubTypeC(subSingle(t, t1, a), subSingle(t, t2, a)))
    return newC


def subSingle(t: FGJ.Type, t1: FGJ.Type, a: FGJ_GT.TypeVarA) -> FGJ.Type:
    match t1:
        case FGJ_GT.TypeVarA(a.name):
            return t
        case FGJ.TypeVar(_):
            return t1
        case FGJ.NonTypeVar(n, ts):
            return FGJ.NonTypeVar(n, FrozenList([subSingle(t, ti, a) for ti in ts]))
    raise Exception("CANT GO HERE - BUT TYPECHECKER")


def occoursIn(a: FGJ_GT.TypeVarA, b: FGJ.Type) -> bool:
    match b:
        case FGJ.TypeVar(_):
            return False
        case FGJ.NonTypeVar(_, ts):
            return any([occoursIn(a, ti) for ti in ts])
        case FGJ_GT.TypeVarA(a.name):
            return True
    raise Exception("CANT GO HERE -> BUT TYPECHECKER")


# genericSupertype
def genericSupertype(C: str, ts: FrozenList[FGJ.Type], D: str, CT: FGJ.ClassTable) -> FrozenList[FGJ.Type]:
    if C == D:
        return ts
    else:
        class_def = CT[C]
        ys = list(class_def.generic_type_annotation.keys())
        superclass = class_def.superclass
        Cprime = superclass.name
        ms = superclass.types
        return genericSupertype(Cprime, FrozenList([AUX.sub(ts, ys, m) for m in ms]), D, CT)


# genericSuperType as List
def genericSupertypeList(C: str, ts: FrozenList[FGJ.Type], D: str, CT: FGJ.ClassTable) -> list[FGJ.Type]:
    if C == D:
        return [FGJ.NonTypeVar(D, ts)]
    else:
        class_def = CT[C]
        ys = list(class_def.generic_type_annotation.keys())
        superclass = class_def.superclass
        Cprime = superclass.name
        ms = superclass.types
        tsPrime = FrozenList([AUX.sub(ts, ys, m) for m in ms])
        return [FGJ.NonTypeVar(C, ts)] + genericSupertypeList(Cprime, tsPrime, D, CT)


def isSubtypeByName(C: str, D: str, CT: FGJ.ClassTable) -> bool:
    if D == "Object":
        return True
    if C == "Object":
        return False
    if C == D:
        return True
    return isSubtypeByName(CT[C].superclass.name, D, CT)


def findCircle(start: FGJ_GT.TypeVarA, a: FGJ_GT.TypeVarA, b: FGJ_GT.TypeVarA, C: FGJ_GT.C) -> list[FGJ_GT.SubTypeC]:
    if start == b:
        return [FGJ_GT.SubTypeC(a, b)]
    for constraint in C:
        match constraint:
            case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(bprime), FGJ_GT.TypeVarA(c)) if b == constraint.t1:
                circle = findCircle(start, FGJ_GT.TypeVarA(bprime), FGJ_GT.TypeVarA(c), C)
                if circle:
                    return [FGJ_GT.SubTypeC(a, b)] + circle
    return []


def isConnected(a: FGJ_GT.TypeVarA, b: FGJ_GT.TypeVarA, C: FGJ_GT.C) -> bool:
    if a == b:
        return True
    for constraint in C:
        match constraint:
            case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(aPrime), FGJ_GT.TypeVarA(c)) if a == FGJ_GT.TypeVarA(aPrime):
                if isConnected(FGJ_GT.TypeVarA(c), b, C):
                    return True
    return False
