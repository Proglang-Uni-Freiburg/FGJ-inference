import FGJ_AST as FGJ

import FGJ_auxiliary_typing as Aux


def typing_expression(expr: FGJ.Expression, Pi: FGJ.Pi, Delta: FGJ.Delta, Env: FGJ.Env, CT: FGJ.ClassTable) -> FGJ.Type:
    match expr:
        case FGJ.Variable():
            return Env[expr]

        case FGJ.FieldLookup(e0, field_name):
            t0 = typing_expression(e0, Pi, Delta, Env, CT)
            typed_fields = Aux.fields(Aux.bound(t0, Delta), CT)
            return typed_fields[field_name]

        case FGJ.MethodLookup(e0, _, method_name, es):
            t0 = typing_expression(e0, Pi, Delta, Env, CT)
            method_sign = Aux.mtype(method_name, Aux.bound(t0, Delta), CT, Pi)
            if not method_sign:
                raise Exception(f"Expression {e0} has no method {method_name}")
            ys = list(method_sign.gen_typ_ano.keys())
            ps = method_sign.gen_typ_ano.values()
            us = method_sign.types_of_arguments
            u = method_sign.return_type
            vs: list[FGJ.Type] = ...  # vs is list[FGJ.Type] and is inferred by FGJ-GT (infer_type(...))
            if not all(Aux.is_well_formed(vi, Delta, CT) for vi in vs):
                raise Exception(f"VS: {vs} is not well typed")
            for vi, pi in zip(vs, ps):
                if not Aux.is_subtype(vi, Aux.substitute_typeVars(vs, ys, pi), Delta, CT):
                    raise Exception(f"Vi: {vi} is not suptype of pi: {pi}")
            for expression, ui in zip(es, us):
                type_of_expr = typing_expression(expression, Pi, Delta, Env, CT)
                if not Aux.is_subtype(type_of_expr, Aux.substitute_typeVars(vs, ys, ui), Delta, CT):
                    raise Exception(f"Argument {expression} is not subtype of {ui}")
            return Aux.substitute_typeVars(vs, ys, u)

        case FGJ.NewClass(type, parameters):
            n: FGJ.NonTypeVar = ...  # asumes some us for N = C<us> (C == type.name)
            if not Aux.is_well_formed(n, Delta, CT):
                raise Exception(f"Type {n} is not well formed")
            typed_fields = Aux.fields(n, CT)
            for expression, ti in zip(parameters, typed_fields.values()):
                type_of_expr = typing_expression(expression, Pi, Delta, Env, CT)
                if not Aux.is_subtype(type_of_expr, ti, Delta, CT):
                    raise Exception(f"Argument {expression} is not suptype of {ti}")
            return n

        case FGJ.Cast(type, expression):
            # We dont use type_of_expression ever?
            # type_of_expression = typing_expression(expression, Pi, Delta, Env, CT)
            return type

        case _:
            raise Exception("CANT GO HERE - BUT TYPECHECKER")


def typing_method(method_def: FGJ.MethodDef, class_def: FGJ.ClassDef, Pi: FGJ.Pi, Delta: FGJ.Delta, CT: FGJ.ClassTable):
    class_header = FGJ.ClassHeader(class_def.name, class_def.generic_type_annotation)
    e0 = method_def.body
    for method_sign in Pi[(class_header, method_def.name)]:
        Env: FGJ.Env = {FGJ.Variable("this"): FGJ.NonTypeVar(class_def.name, list(class_def.generic_type_annotation.keys()))}
        ts = method_sign.types_of_arguments
        for x, ti in zip(method_def.typed_parameters.keys(), ts):
            Env[FGJ.Variable(x)] = ti
        s = typing_expression(e0, Pi, Delta, Env, CT)
        t = method_sign.return_type
        if not Aux.is_subtype(s, t, Delta, CT):
            raise Exception(f"Returned type {s} is not subtype of {t}")
        name_of_superclass = class_def.superclass.name
        if name_of_superclass != "Object":
            ysEps: FGJ.GenTypeAno = ... # infered
            if not Aux.is_valid_method_override(method_def.name, class_def.superclass, FGJ.MethodSign(ysEps, ts, t), CT, Pi):
                raise Exception("Not valid override")


def typing_class(class_def: FGJ.ClassDef, Pi: FGJ.Pi, CT: FGJ.ClassTable):
    ysEps: FGJ.GenTypeAno = ...  # infered
    # can return values be None? if yes things go wrong here!
    Pi1 = Pi | {(FGJ.ClassHeader(class_def.name, class_def.generic_type_annotation), method_def.name): {FGJ.MethodSign(dict(), list(method_def.typed_parameters.values()), method_def.return_type)} for method_def in class_def.methods.values() if method_def.return_type}
    Pi2 = Pi | {(FGJ.ClassHeader(class_def.name, ysEps), method_def.name): {FGJ.MethodSign(method_def.generic_type_annotation, list(method_def.typed_parameters.values()), method_def.return_type)} for method_def in class_def.methods.values() if method_def.return_type}
    xsEns = class_def.generic_type_annotation
    Delta = xsEns | ysEps
    ps = list(ysEps.values())
    if not all(Aux.is_well_formed(pi, Delta, CT) for pi in ps):
        raise Exception(f"{ps} is not well typed")
    for method in class_def.methods.values():
        if not all(Aux.is_well_formed(ti, Delta, CT) for ti in method.typed_parameters.values()):
            raise Exception(f"Argtypes of method {method} are not well formed")
        if not method.return_type:
            raise Exception("Method Returntype is None - CAN I GO HERE?")
        if not Aux.is_well_formed(method.return_type, Delta, CT):
            raise Exception(f"Return Type of method {method} is not well formed")
    if not all(Aux.is_well_formed(ni, xsEns, CT) for ni in class_def.generic_type_annotation.values()):
        raise Exception(f"Upper bounds of class {class_def.name} is not well formed")
    if not Aux.is_well_formed(class_def.superclass, xsEns, CT):
        raise Exception(f"Superclass of class {class_def.name} is not well typed")
    if not all(Aux.is_well_formed(ti, xsEns, CT) for ti in class_def.typed_fields.values()):
        raise Exception(f"Fields of {class_def.name} is not well formed")
    for method in class_def.methods.values():
        typing_method(method, class_def, Pi1, Delta, CT)  # with <Ys extends Ps> ?
    # skip constructor
    return Pi2


def typing_program(CT: FGJ.ClassTable) -> FGJ.Pi:
    pii: FGJ.Pi = dict()
    for class_def in CT.values():
        pii |= typing_class(class_def, pii, CT)
    return pii
