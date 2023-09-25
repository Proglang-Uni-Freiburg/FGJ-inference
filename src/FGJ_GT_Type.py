import FGJ_AST as FGJ
import FGJ_GT_AST as FGJ_GT
import FGJ_auxiliary_typing as AUX

from FGJ_GT_auxiliary_functions import fresh
from frozendict import frozendict
from frozenlist import FrozenList


fresh_a = fresh("a")
fresh_b = fresh("b")


def FJType(Pi: FGJ.Pi, class_def: FGJ.ClassDef, CT: FGJ.ClassTable) -> tuple[FGJ_GT.lambdas, FGJ_GT.C]:
    class_header = FGJ.ClassHeader(class_def.name, frozendict(class_def.generic_type_annotation.items()))
    l0s: dict[tuple[FGJ.ClassHeader, str], list[FGJ.MethodSign]] = dict()
    C0e: FGJ_GT.C = frozenset()
    ls: dict[tuple[FGJ.ClassHeader, str], list[FGJ.MethodSign]] = dict()
    Cm: FGJ_GT.C = frozenset()
    for method_def in class_def.methods.values():
        method_sign = AUX.mtype(method_def.name, class_def.superclass, CT, Pi)
        am = next(fresh_a)
        if method_sign:
            # OWN NOT PROOFED YET
            print(">", method_def.name, method_sign.gen_typ_ano)
            l0s[(class_header, method_def.name)] = [FGJ.MethodSign(dict(method_sign.gen_typ_ano.items()), method_sign.types_of_arguments, am)]
            # original:
            # l0s[(class_header, method_def.name)] = [FGJ.MethodSign(dict(method_sign.gen_typ_ano.items()), method_sign.types_of_arguments, am)]
            C0e |= frozenset([FGJ_GT.SubTypeC(am, method_sign.return_type)])
        else:
            ass: list[FGJ.Type] = [next(fresh_a) for _ in method_def.typed_parameters]
            ls[(class_header, method_def.name)] = [FGJ.MethodSign(dict(), ass, am)]
            Cm |= frozenset([FGJ_GT.SubTypeC(am, FGJ.NonTypeVar("Object", FrozenList()))]) | frozenset([FGJ_GT.SubTypeC(ai, FGJ.NonTypeVar("Object", FrozenList())) for ai in ass])
    BigPi = Pi | l0s | ls
    constraints = C0e | Cm
    for method_def in class_def.methods.values():
        constraints |= TypeMethod(BigPi, class_header, method_def, CT)
    return BigPi, constraints


def TypeMethod(Pi: FGJ.Pi, class_header: FGJ.ClassHeader, method_def: FGJ.MethodDef, CT: FGJ.ClassTable) -> FGJ_GT.C:
    method_sign = Pi[(class_header, method_def.name)][0]  # ????
    Re, Ce = TypeExpr((Pi, {FGJ.Variable("this"): FGJ.NonTypeVar(class_header.class_name, FrozenList(class_header.bounded_types.keys()))} | {FGJ.Variable(x): T for x, T in zip(method_def.typed_parameters.keys(), method_sign.types_of_arguments)}), method_def.body, CT)
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
                a1s: FrozenList[FGJ.Type] = FrozenList([next(fresh_a) for _ in class_def.generic_type_annotation.values()])
                xs = list(class_def.generic_type_annotation.keys())
                c_new: FGJ_GT.C = frozenset([FGJ_GT.SubTypeC(Re, FGJ.NonTypeVar(class_def.name, a1s)),
                                             FGJ_GT.EqualC(a, AUX.substitute_typeVars(a1s, xs, class_def.typed_fields[name])),
                                             ])
                for ai, ni in zip(a1s, class_def.generic_type_annotation.values()):
                    c_new |= frozenset([FGJ_GT.SubTypeC(ai, AUX.substitute_typeVars(a1s, xs, ni))])
                oc |= frozenset([c_new])
            return a, Cr | frozenset([oc])

        case FGJ.MethodLookup(e0, _, name, parameters):
            Re, Cr = TypeExpr(teta, e0, CT)
            RiCi = [TypeExpr(teta, ei, CT) for ei in parameters]
            Ri = map(lambda t: t[0], RiCi)
            Ci = set(map(lambda t: t[1], RiCi))
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
                        ass1: FrozenList[FGJ.Type] = FrozenList([next(fresh_a) for _ in class_header.bounded_types])
                        bs: FrozenList[FGJ.Type] = FrozenList([next(fresh_b) for _ in method_sign.gen_typ_ano])
                        oc |= frozenset([frozenset([FGJ_GT.SubTypeC(Re, FGJ.NonTypeVar(class_header.class_name, ass1))]) |
                                         frozenset([FGJ_GT.EqualC(a, AUX.substitute_typeVars(bs, ys, AUX.substitute_typeVars(ass1, xs, t)))]) |
                                         frozenset([FGJ_GT.SubTypeC(Ri, AUX.substitute_typeVars(bs, ys, AUX.substitute_typeVars(ass1, xs, ti))) for Ri, ti in zip(Ri, ts)]) |
                                         frozenset([FGJ_GT.SubTypeC(bi, AUX.substitute_typeVars(bs, ys, AUX.substitute_typeVars(ass1, xs, pi))) for bi, pi in zip(bs, ps)]) |
                                         frozenset([FGJ_GT.SubTypeC(ai, AUX.substitute_typeVars(ass1, xs, ni)) for ai, ni in zip(ass1, ns)])
                                         ])
            c_ret = Cr | frozenset([oc])
            for ci in Ci:
                c_ret |= ci
            return a, c_ret

        case FGJ.NewClass(type1, parameters):
            RiCi = [TypeExpr(teta, expr, CT) for expr in parameters]
            ass: FrozenList[FGJ.Type] = FrozenList([next(fresh_a) for _ in parameters])
            ca = FGJ.NonTypeVar(type1.name, ass)
            typed_fields = AUX.fields(ca, CT)
            if type1.name == "Object":
                xs = []
                ns = []
            else:
                xs = list(CT[type1.name].generic_type_annotation.keys())
                ns = list(CT[type1.name].generic_type_annotation.values())
            sc = frozenset([FGJ_GT.SubTypeC(Ri, ti) for Ri, ti in zip(map(lambda t: t[0], RiCi), typed_fields.values())]) | frozenset([FGJ_GT.SubTypeC(ai, AUX.substitute_typeVars(ass, xs, ni)) for ai, ni in zip(ass, ns)])
            for constraint in map(lambda t: t[1], RiCi):
                sc |= constraint
            return ca, sc

        case FGJ.Cast(type1, expr):
            _, Cr = TypeExpr(teta, expr, CT)
            return type1, Cr

        case _:
            raise Exception("CANT GO HERE - BUT TYPECHECKER", type(expr))
