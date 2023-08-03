from typing import Generator, Any
import FGJ_AST as FGJ
import FGJ_GT_AST as FGJ_GT
import FGJ_auxiliary_typing as AUX


def fresh(name: str) -> Generator[FGJ_GT.TypeVarA, Any, None]:
    count = 0
    while True:
        yield FGJ_GT.TypeVarA(name + str(count))
        count += 1


def TypeInference(Pi: FGJ.Pi, class_def: FGJ.ClassDef, CT: FGJ.ClassTable) -> FGJ.Pi:
    ls, constraint = FJType(Pi, class_def, CT)  # constraint generation
    sig, ysEps = Unify(constraint, class_def.generic_type_annotation, CT)  # constraint solving
    # set or single? (set(MethodSign))
    return Pi | {class_header_method_tuple: {FGJ.MethodSign(ysEps, [sig(ai) for ai in method_sign.types_of_arguments], sig(method_sign.return_type))} for class_header_method_tuple, method_sign in ls.items()}


fresh_a = fresh("a")
fresh_b = fresh("b")


def FJType(Pi: FGJ.Pi, class_def: FGJ.ClassDef, CT: FGJ.ClassTable) -> tuple[FGJ_GT.lambdas, FGJ_GT.C]:
    class_header = FGJ.ClassHeader(class_def.name, dict(class_def.generic_type_annotation.items()))
    l0s: dict[tuple[FGJ.ClassHeader, str], set[FGJ.MethodSign]] = dict()
    C0e: set[FGJ_GT.SubTypeC] = set()
    ls: dict[tuple[FGJ.ClassHeader, str], set[FGJ.MethodSign]] = dict()
    Cm: set[FGJ_GT.SubTypeC] = set()
    for method_def in class_def.methods.values():
        method_sign = AUX.mtype(method_def.name, class_def.superclass, CT, Pi)
        am = next(fresh_a)
        if method_sign:
            l0s[(class_header, method_def.name)] = {FGJ.MethodSign(dict(method_sign.gen_typ_ano.items()), method_sign.types_of_arguments, am)}
            C0e |= {FGJ_GT.SubTypeC(am, method_sign.return_type)}
        else:
            ass: list[FGJ.Type] = [next(fresh_a) for _ in method_def.typed_parameters]
            ls[(class_header, method_def.name)] = {FGJ.MethodSign(dict(), ass, am)}
            Cm |= {FGJ_GT.SubTypeC(am, FGJ.NonTypeVar("Object", []))} | {FGJ_GT.SubTypeC(ai, FGJ.NonTypeVar("Object", [])) for ai in ass}
    BigPi = Pi | l0s | ls
    constraints = C0e | Cm
    for method_def in class_def.methods.values():
        constraints |= TypeMethod(BigPi, class_header, method_def, CT)
    return BigPi, constraints


def TypeMethod(Pi: FGJ.Pi, class_header: FGJ.ClassHeader, method_def: FGJ.MethodDef, CT: FGJ.ClassTable) -> FGJ_GT.C:
    method_sign = list(Pi[(class_header, method_def.name)])[0]  # ????
    Re, Ce = TypeExpr((Pi, {FGJ.Variable("this"): FGJ.NonTypeVar(class_header.class_name, list(class_header.bounded_types.keys()))} | {FGJ.Variable(x): T for x, T in zip(method_def.typed_parameters.keys(), method_sign.types_of_arguments)}), method_def.body, CT)
    return Ce | {FGJ_GT.SubTypeC(Re, method_sign.return_type)}


def TypeExpr(teta: FGJ_GT.Teta, expr: FGJ.Expression, CT: FGJ.ClassTable) -> tuple[FGJ.Type, FGJ_GT.C]:
    Pi, µ = teta
    match expr:
        case FGJ.Variable(_):
            return µ[expr], set()

        case FGJ.FieldLookup(e0, name):
            Re, Cr = TypeExpr(teta, e0, CT)
            a = next(fresh_a)
            oc: FGJ_GT.oc = set()
            for class_def in CT.values():
                if name not in class_def.typed_fields.keys():
                    continue
                a1s: list[FGJ.Type] = [next(fresh_a) for _ in class_def.generic_type_annotation.values()]
                xs = list(class_def.generic_type_annotation.keys())
                c_new = {FGJ_GT.SubTypeC(Re, FGJ.NonTypeVar(class_def.name, a1s)),
                         FGJ_GT.EqualC(a, AUX.sub(a1s, xs, class_def.typed_fields[name])),
                         }
                for ai, ni in zip(a1s, class_def.generic_type_annotation.values()):
                    c_new |= {FGJ_GT.SubTypeC(ai, AUX.sub(a1s, xs, ni))}
                oc |= {c_new} # not hashable ...
            return a, Cr | {oc}

        case FGJ.MethodLookup(e0, _, name, parameters):
            Re, Cr = TypeExpr(teta, e0, CT)
            RiCi = dict(TypeExpr(teta, ei, CT) for ei in parameters)
            Ri = RiCi.keys()
            Ci = set(RiCi.values())
            a = next(fresh_a)
            oc: FGJ_GT.oc = set()
            for elem in Pi.items():
                match elem:
                    case ((_, method_name), _) if method_name != name:
                        continue
                    case ((class_header, method_name), set_of_method_sign):
                        method_sign = list(set_of_method_sign)[0]
                        xs = class_header.bounded_types.keys()
                        ns = class_header.bounded_types.values()
                        ys = method_sign.gen_typ_ano.keys()
                        ps = method_sign.gen_typ_ano.values()
                        ts = method_sign.types_of_arguments
                        t = method_sign.return_type
                        ass = [next(fresh_a) for _ in class_header.bounded_types]
                        bs = [next(fresh_b) for _ in class_header.bounded_types]
                        oc |= {{FGJ_GT.SubTypeC(Re, FGJ.NonTypeVar(class_header.class_name, ai)) for ai in ass} |
                              {FGJ_GT.EqualC(a, AUX.sub(bs, ys, AUX.sub(ass, xs, t)))} |
                              {FGJ_GT.SubTypeC(Ri, AUX.sub(bs, ys, AUX.sub(ass, xs, ti))) for Ri, ti in zip(Ri, ts)} |
                              {FGJ_GT.SubTypeC(bi, AUX.sub(bs, ys, AUX.sub(ass, xs, pi))) for bi, pi in zip(bs, ps)} |
                              {FGJ_GT.SubTypeC(ai, AUX.sub(ass, xs, ni)) for ai, ni in zip(ass, ns)}
                              }
            c_ret = Cr | {oc}
            for ci in Ci:
                c_ret |= ci
            return a, c_ret

        case FGJ.NewClass(type, parameters):
            RiCi = dict(TypeExpr(teta, expr, CT) for expr in parameters)
            ass: list[FGJ.Type] = [next(fresh_a) for _ in parameters]
            ca = FGJ.NonTypeVar(type.name, ass)
            typed_fields = AUX.fields(ca, CT)
            xs = list(CT[type.name].generic_type_annotation.keys())
            ns = list(CT[type.name].generic_type_annotation.values())
            sc = {FGJ_GT.SubTypeC(Ri, ti) for Ri, ti in zip(RiCi.keys(), typed_fields.values())} | {FGJ_GT.SubTypeC(ai, AUX.sub(ass, xs, ni)) for ai, ni in zip(ass, ns)}
            for constraint in RiCi.values():
                sc |= constraint
            return ca, sc

        case _:
            raise Exception("CANT GO HERE - BUT TYPECHECKER")


# Constraint solving # laufzeit tot?

def is_solved_form(C: FGJ_GT.C) -> bool:
    as_12: list[str] = list()
    as_34: list[str] = list()
    for constraint in C:
        match constraint:
            case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA()) if a not in as_34:
                as_12.append(a)
            case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar()) if a not in as_12:
                as_34.append(a)
            case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA()) if a not in as_34:
                as_12.append(a)
            case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(_, ts)) if constraint.t1 not in ts and a not in as_12:
                as_34.append(a)
            case _:
                return False
    return True


def gen_C_prime(C: FGJ_GT.C) -> Generator[set[FGJ_GT.sc], Any, Any]:
    sc_set: set[FGJ_GT.sc] = set()
    oc_list: list[FGJ_GT.oc] = list()
    for c in C:
        match c:
            case FGJ_GT.SubTypeC():
                sc_set |= {c}
            case FGJ_GT.EqualC():
                sc_set |= {c}
            case _:
                oc_list += [c]
    for oc in oc_list:
        out_set: set[FGJ_GT.sc] = set()
        for sci in oc:
            out_set |= sci
        yield out_set | sc_set


def Unify(C: FGJ_GT.C, env: FGJ.Delta, CT: FGJ.ClassTable):
    for C_prime in gen_C_prime(C):
        # step 1
        changes = True
        while changes:
            changes = False
            for constraint in C_prime:
                match constraint:
                    # 1 Argument

                    # adapt
                    case FGJ_GT.SubTypeC(FGJ.NonTypeVar(n1, ts), FGJ.NonTypeVar(n2, us)) if isSubtypeByName(n1, n2, CT):
                        xs: list[FGJ.Type] = [FGJ.TypeVar("x" + str(i)) for i, _ in enumerate(ts)]
                        ns = genericSupertype(n1, xs, n2, CT)
                        C.remove(constraint)
                        subtedns = [AUX.sub(ts, xs, ni) for ni in ns]
                        C |= {FGJ_GT.EqualC(FGJ.NonTypeVar(n2, subtedns), FGJ.NonTypeVar(n2, us))}
                        changes = True

                    case FGJ_GT.SubTypeC(FGJ.TypeVar(n1), FGJ.NonTypeVar(n2, us)) if isSubtypeByName(env[FGJ.TypeVar(n1)].name, n2, CT):
                        ns = genericSupertype(env[FGJ.TypeVar(n1)].name, env[FGJ.TypeVar(n1)].types, n2, CT)
                        C.remove(constraint)
                        C |= {FGJ_GT.EqualC(FGJ.NonTypeVar(n2, ns), FGJ.NonTypeVar(n2, us))}
                        changes = True

                    # reduce
                    case FGJ_GT.SubTypeC(FGJ.NonTypeVar(c, ts), FGJ.NonTypeVar(d, us)) if c == d:
                        C.remove(constraint)
                        C |= {FGJ_GT.EqualC(ti, ui) for ti, ui in zip(ts, us)}
                        changes = True

                    # equals
                    case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b)):
                        equals: list[FGJ_GT.SubTypeC] = findCircle(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b), C)
                        for sc in equals:
                            C.remove(sc)
                            C.add(FGJ_GT.EqualC(sc.t1, sc.t2))
                            changes = True

                    # erase
                    case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b)) if a == b:
                        C.remove(constraint)
                        changes = True

                    case FGJ_GT.EqualC(FGJ.TypeVar(x), FGJ.TypeVar(y)) if x == y:
                        C.remove(constraint)
                        changes = True

                    # swap
                    case FGJ_GT.EqualC(FGJ.NonTypeVar(n, ts), FGJ_GT.TypeVarA(a)):
                        C.remove(constraint)
                        C.add(FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(n, ts)))
                        changes = True

                    # 2 Arguments
                for constraint2 in C_prime:
                    if constraint == constraint2:
                        continue

                    match constraint, constraint2:

                        # match
                        case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(c, _)), FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(d, _)) if a == b:
                            if isSubtypeByName(c, d, CT):
                                C.remove(constraint2)
                                C.add(FGJ_GT.SubTypeC(constraint.t2, constraint2.t2))
                                changes = True
                            elif isSubtypeByName(d, c, CT):
                                C.remove(constraint)
                                C.add(FGJ_GT.SubTypeC(constraint2.t2, constraint.t2))
                                changes = True

                        # adopt
                        case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(c, cs)), FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(d, _)) if isConnected(FGJ_GT.TypeVarA(b), FGJ_GT.TypeVarA(a), C):
                            C.add(FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(c, cs)))
                            changes = True


# genericSupertype
def genericSupertype(C: str, ts: list[FGJ.Type], D: str, CT: FGJ.ClassTable) -> list[FGJ.Type]:
    if C == D:
        return ts
    else:
        class_def = CT[C]
        ys = list(class_def.generic_type_annotation.keys())
        superclass = class_def.superclass
        Cprime = superclass.name
        ms = superclass.types
        return genericSupertype(Cprime, [AUX.sub(ts, ys, m) for m in ms], D, CT)


def isSubtypeByName(C: str, D: str, CT: FGJ.ClassTable) -> bool:
    if D == "Object":
        return True
    if C == "Object":
        return False
    if C == D:
        return True
    return isSubtypeByName(CT[C].superclass.name, D, CT)


# findCircle
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


# connected
def isConnected(a: FGJ_GT.TypeVarA, b: FGJ_GT.TypeVarA, C: FGJ_GT.C) -> bool:
    if a == b:
        return True
    for constraint in C:
        match constraint:
            case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(aPrime), FGJ_GT.TypeVarA(c)) if a == FGJ_GT.TypeVarA(aPrime):
                if isConnected(FGJ_GT.TypeVarA(c), b, C):
                    return True
    return False
