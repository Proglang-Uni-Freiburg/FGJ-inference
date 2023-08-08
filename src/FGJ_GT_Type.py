import FGJ_AST as FGJ
import FGJ_GT_AST as FGJ_GT
import FGJ_auxiliary_typing as AUX

from FGJ_GT_auxiliary_functions import fresh


fresh_a = fresh("a")
fresh_b = fresh("b")


def FJType(Pi: FGJ.Pi, class_def: FGJ.ClassDef, CT: FGJ.ClassTable) -> tuple[FGJ_GT.lambdas, FGJ_GT.C]:
    class_header = FGJ.ClassHeader(class_def.name, dict(class_def.generic_type_annotation.items()))
    l0s: dict[tuple[FGJ.ClassHeader, str], frozenset[FGJ.MethodSign]] = dict()
    C0e: FGJ_GT.C = frozenset()
    ls: dict[tuple[FGJ.ClassHeader, str], frozenset[FGJ.MethodSign]] = dict()
    Cm: FGJ_GT.C = frozenset()
    for method_def in class_def.methods.values():
        method_sign = AUX.mtype(method_def.name, class_def.superclass, CT, Pi)
        am = next(fresh_a)
        if method_sign:
            l0s[(class_header, method_def.name)] = frozenset([FGJ.MethodSign(dict(method_sign.gen_typ_ano.items()), method_sign.types_of_arguments, am)])
            C0e |= frozenset([FGJ_GT.SubTypeC(am, method_sign.return_type)])
        else:
            ass: list[FGJ.Type] = [next(fresh_a) for _ in method_def.typed_parameters]
            ls[(class_header, method_def.name)] = frozenset([FGJ.MethodSign(dict(), ass, am)])
            Cm |= frozenset([FGJ_GT.SubTypeC(am, FGJ.NonTypeVar("Object", []))]) | frozenset([FGJ_GT.SubTypeC(ai, FGJ.NonTypeVar("Object", [])) for ai in ass])
    BigPi = Pi | l0s | ls
    constraints = C0e | Cm
    for method_def in class_def.methods.values():
        constraints |= TypeMethod(BigPi, class_header, method_def, CT)
    return BigPi, constraints


def TypeMethod(Pi: FGJ.Pi, class_header: FGJ.ClassHeader, method_def: FGJ.MethodDef, CT: FGJ.ClassTable) -> FGJ_GT.C:
    method_sign = list(Pi[(class_header, method_def.name)])[0]  # ????
    Re, Ce = TypeExpr((Pi, {FGJ.Variable("this"): FGJ.NonTypeVar(class_header.class_name, list(class_header.bounded_types.keys()))} | {FGJ.Variable(x): T for x, T in zip(method_def.typed_parameters.keys(), method_sign.types_of_arguments)}), method_def.body, CT)
    return Ce | frozenset([FGJ_GT.SubTypeC(Re, method_sign.return_type)])


def TypeExpr(teta: FGJ_GT.Teta, expr: FGJ.Expression, CT: FGJ.ClassTable) -> tuple[FGJ.Type, FGJ_GT.C]:
    Pi, µ = teta
    match expr:
        case FGJ.Variable(_):
            return µ[expr], frozenset()

        case FGJ.FieldLookup(e0, name):
            Re, Cr = TypeExpr(teta, e0, CT)
            a = next(fresh_a)
            oc: FGJ_GT.oc = frozenset()
            for class_def in CT.values():
                if name not in class_def.typed_fields.keys():
                    continue
                a1s: list[FGJ.Type] = [next(fresh_a) for _ in class_def.generic_type_annotation.values()]
                xs = list(class_def.generic_type_annotation.keys())
                c_new: FGJ_GT.C = frozenset([FGJ_GT.SubTypeC(Re, FGJ.NonTypeVar(class_def.name, a1s)),
                                             FGJ_GT.EqualC(a, AUX.sub(a1s, xs, class_def.typed_fields[name])),
                                             ])
                for ai, ni in zip(a1s, class_def.generic_type_annotation.values()):
                    c_new |= frozenset([FGJ_GT.SubTypeC(ai, AUX.sub(a1s, xs, ni))])
                oc |= frozenset([c_new])
            return a, Cr | frozenset([oc])

        case FGJ.MethodLookup(e0, _, name, parameters):
            Re, Cr = TypeExpr(teta, e0, CT)
            RiCi = dict(TypeExpr(teta, ei, CT) for ei in parameters)
            Ri = RiCi.keys()
            Ci = set(RiCi.values())
            a = next(fresh_a)
            oc: FGJ_GT.oc = frozenset()
            for elem in Pi.items():
                match elem:
                    case ((_, method_name), _) if method_name != name:
                        continue
                    case ((class_header, method_name), set_of_method_sign):
                        method_sign = list(set_of_method_sign)[0]
                        xs = list(class_header.bounded_types.keys())
                        ns = list(class_header.bounded_types.values())
                        ys = list(method_sign.gen_typ_ano.keys())
                        ps = list(method_sign.gen_typ_ano.values())
                        ts = method_sign.types_of_arguments
                        t = method_sign.return_type
                        ass = [next(fresh_a) for _ in class_header.bounded_types]
                        bs: list[FGJ.Type] = [next(fresh_b) for _ in class_header.bounded_types]
                        oc |= frozenset([frozenset([FGJ_GT.SubTypeC(Re, FGJ.NonTypeVar(class_header.class_name, ass))]) |
                                         frozenset([FGJ_GT.EqualC(a, AUX.sub(bs, ys, AUX.sub(ass, xs, t)))]) |
                                         frozenset([FGJ_GT.SubTypeC(Ri, AUX.sub(bs, ys, AUX.sub(ass, xs, ti))) for Ri, ti in zip(Ri, ts)]) |
                                         frozenset([FGJ_GT.SubTypeC(bi, AUX.sub(bs, ys, AUX.sub(ass, xs, pi))) for bi, pi in zip(bs, ps)]) |
                                         frozenset([FGJ_GT.SubTypeC(ai, AUX.sub(ass, xs, ni)) for ai, ni in zip(ass, ns)])
                                         ])
            c_ret = Cr | frozenset([oc])
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
            sc = frozenset([FGJ_GT.SubTypeC(Ri, ti) for Ri, ti in zip(RiCi.keys(), typed_fields.values())]) | hSet([FGJ_GT.SubTypeC(ai, AUX.sub(ass, xs, ni)) for ai, ni in zip(ass, ns)])
            for constraint in RiCi.values():
                sc |= constraint
            return ca, sc

        case _:
            raise Exception("CANT GO HERE - BUT TYPECHECKER")
