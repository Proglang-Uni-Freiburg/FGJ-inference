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
    sig, ysEps = Unify(constraint, class_def.generic_type_annotation)  # constraint solving
    # set or single? (set(MethodSign))
    return Pi | {class_header_method_tuple: FGJ.MethodSign(ysEps, [sig(ai) for ai in method_sign_A.types_of_arguments], sig(method_sign_A.return_type)) for class_header_method_tuple, method_sign_A in ls.items()}


fresh_a = fresh("a")
fresh_b = fresh("b")


def FJType(Pi: FGJ.Pi, class_def: FGJ.ClassDef, CT: FGJ.ClassTable) -> tuple[FGJ_GT.lambdas, FGJ_GT.C]:
    class_header = FGJ_GT.ClassHeaderA(class_def.name, class_def.generic_type_annotation.items())
    l0s: dict[tuple[FGJ_GT.ClassHeaderA, str], set[FGJ_GT.MethodSignA]] = dict()
    C0e: set[FGJ_GT.SubTypeC] = set()
    ls: dict[tuple[FGJ_GT.ClassHeaderA, str], set[FGJ_GT.MethodSignA]] = dict()
    Cm: set[FGJ_GT.SubTypeC] = set()
    for method_def in class_def.methods.values():
        method_sign = AUX.mtype(method_def.name, class_def.superclass, CT, Pi)
        am = next(fresh_a)
        if method_sign:
            l0s[(class_header, method_def.name)] = FGJ_GT.MethodSignA({FGJ_GT.BoundedTypeVarA(x.name): FGJ_GT.NonTypeVarA(n.name, [FGJ_GT.to_TypeA(t) for t in n.types]) for x, n in method_sign.gen_typ_ano.items()}, [FGJ_GT.to_TypeA(t) for t in method_sign.types_of_arguments], am)
            C0e |= {FGJ_GT.SubTypeC(am, FGJ_GT.to_TypeA(method_sign.return_type))}
        else:
            ass = [next(fresh_a) for _ in method_def.typed_parameters]
            ls[(class_header, method_def.name)] = {FGJ_GT.MethodSignA(dict(), ass, am)}
            Cm |= {FGJ_GT.SubTypeC(am, FGJ_GT.NonTypeVarA("Object", []))} | {FGJ_GT.SubTypeC(ai, FGJ_GT.NonTypeVarA("Object", [])) for ai in ass}
    BigPi = Pi | l0s | ls
    constraints = C0e | Cm
    for method_def in class_def.methods.values():
        constraints |= TypeMethod(BigPi, class_header, method_def, CT)
    return BigPi, constraints


def TypeMethod(Pi: FGJ.Pi, class_header: FGJ_GT.ClassHeaderA, method_def: FGJ.MethodDef, CT: FGJ.ClassTable) -> FGJ_GT.C:
    method_sign = list(Pi[(class_header, method_def.name)])[0]  # ????
    Re, Ce = TypeExpr((Pi, {FGJ.Variable("this"): FGJ_GT.NonTypeVarA(class_header.class_name, class_header.bounded_types.keys())} | {x: T for x, T in zip(method_def.typed_parameters.keys(), method_sign.types_of_arguments)}), method_def.body, CT)
    return Ce | {FGJ_GT.SubTypeC(Re, method_sign.return_type)}


def TypeExpr(teta: FGJ_GT.Teta, expr: FGJ.Expression, CT: FGJ.ClassTable) -> tuple[FGJ_GT.TypeA, FGJ_GT.C]:
    Pi, µ = teta
    match expr:
        case FGJ.Variable(_):
            return µ[expr], set()

        case FGJ.FieldLookup(e0, name):
            Re, Cr = TypeExpr(teta, e0, CT)
            a = next(fresh_a)
            oc: set[set[FGJ_GT.sc]] = set()
            for class_def in CT.values():
                if name not in class_def.typed_fields.keys():
                    continue
                a1s = [next(fresh_a) for _ in class_def.generic_type_annotation.values()]
                xs = class_def.generic_type_annotation.keys()
                oc |= {{FGJ_GT.SubTypeC(Re, FGJ_GT.NonTypeVarA(class_def.name, a1s)),
                        FGJ_GT.EqualC(a, AUX.sub(a1s, xs, class_def.typed_fields[name])),
                        } | {FGJ_GT.SubTypeC(ai, AUX.sub(a1s, xs, ni)) for ai, ni in zip(a1s, class_def.generic_type_annotation.values())}}
            return a, Cr | oc

        case FGJ.MethodLookup(e0, _, name, parameters):
            Re, Cr = TypeExpr(teta, e0, CT)
            RiCi = dict(TypeExpr(teta, ei, CT) for ei in parameters)
            Ri = RiCi.keys()
            Ci = RiCi.values()
            a = next(fresh_a)
            c: FGJ_GT.oc = set()
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
                        c |= {{FGJ_GT.SubTypeC(Re, FGJ_GT.NonTypeVarA(class_header.class_name, ai)) for ai in ass} |
                              {FGJ_GT.EqualC(a, AUX.sub(bs, ys, AUX.sub(ass, xs, t)))} |
                              {FGJ_GT.SubTypeC(Ri, AUX.sub(bs, ys, AUX.sub(ass, xs, ti))) for Ri, ti in zip(Ri, ts)} |
                              {FGJ_GT.SubTypeC(bi, AUX.sub(bs, ys, AUX.sub(ass, xs, pi))) for bi, pi in zip(bs, ps)} |
                              {FGJ_GT.SubTypeC(ai, AUX.sub(ass, xs, ni)) for ai, ni in zip(ass, ns)}
                              }
            return a, Cr | {ci for ci in Ci} | {c}

        case FGJ.NewClass(type, parameters):
            RiCi = dict(TypeExpr(teta, expr, CT) for expr in parameters)
            ass = [next(fresh_a) for _ in parameters]
            ca = FGJ_GT.NonTypeVarA(type.name, ass)
            typed_fields = AUX.fields(ca, CT)
            xs = CT[type.name].generic_type_annotation.keys()
            ns = CT[type.name].generic_type_annotation.values()
            C = {FGJ_GT.SubTypeC(Ri, ti) for Ri, ti in zip(RiCi.keys(), typed_fields.values())} | {FGJ_GT.SubTypeC(ai, AUX.sub(ass, xs, ni)) for ai, ni in zip(ass, ns)}
            return ca, C | {ci for ci in RiCi.values()}

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
            case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ_GT.NonTypeVarA()) if a not in as_12:
                as_34.append(a)
            case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA()) if a not in as_34:
                as_12.append(a)
            case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ_GT.NonTypeVarA(_, ts)) if FGJ_GT.TypeVarA(a) not in ts and a not in as_12:
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


def Unify(C: FGJ_GT.C, env: FGJ.Delta):
    for C_prime in gen_C_prime(C):
        # step 1
        changes = True
        while changes:
            changes = False
            for constraint in C_prime:
                match constraint:
                    # adapt
                    # reduce
                    case FGJ_GT.SubTypeC(FGJ_GT.NonTypeVarA(c, ts), FGJ_GT.NonTypeVarA(d, us)) if c == d:
                        C.remove(constraint)
                        C |= {FGJ_GT.EqualC(ti, ui) for ti, ui in zip(ts, us)}
                        changes = True
                    # erase
                    case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b)) if a == b:
                        C.remove(constraint)
                        changes = True
                    # swap
                    case FGJ_GT.EqualC(FGJ_GT.NonTypeVarA(n, ts), FGJ_GT.TypeVarA(a)):
                        C.remove(constraint)
                        C.add(FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ_GT.NonTypeVarA(n, ts)))
                        changes = True
