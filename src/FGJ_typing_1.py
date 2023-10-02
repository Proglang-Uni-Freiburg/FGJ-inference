import FGJ_AST as FGJ
import FGJ_auxiliary_typing as AUX_T

from frozenlist import FrozenList
from frozendict import frozendict


def TypeExpr(expr: FGJ.Expression, Delta: FGJ.Delta, Gamma: dict[FGJ.Variable, FGJ.Type], CT: FGJ.ClassTable, Pi: FGJ.Pi) -> FGJ.Type:
    match expr:
        case FGJ.Variable(_):
            return Gamma[expr]

        case FGJ.FieldLookup(e, field_name):
            t0 = TypeExpr(e, Delta, Gamma, CT, Pi)
            typed_fields = AUX_T.fields(AUX_T.bound(t0, Delta), CT)
            return typed_fields[field_name]

        case FGJ.MethodLookup(e, _, method_name, parameters):
            t0 = TypeExpr(e, Delta, Gamma, CT, Pi)
            method_sign = AUX_T.mtype(method_name, AUX_T.bound(t0, Delta), CT, Pi)
            if method_sign is None:
                raise Exception("Method type not found (None)")
            for parameter, t in zip(parameters, method_sign.types_of_arguments):
                tp = TypeExpr(parameter, Delta, Gamma, CT, Pi)
                if not AUX_T.is_subtype(tp, t, Delta, CT):
                    raise Exception(f"{tp} is not a subtype of {t} in method {method_name}")
            return method_sign.return_type

        case FGJ.NewClass(t, parameters):
            if not AUX_T.is_well_formed(t, Delta, CT):
                raise Exception(f"{t} is not well formed")
            typed_fields = AUX_T.fields(t, CT)
            types_of_parameters = [TypeExpr(parameter, Delta, Gamma, CT, Pi) for parameter in parameters]
            for parameter, type_of_parameter, field_type in zip(parameters, types_of_parameters, typed_fields.values()):
                if not AUX_T.is_subtype(type_of_parameter, field_type, Delta, CT):
                    raise Exception(f"{parameter} is not a subtype of {field_type}")
            return FGJ.NonTypeVar(t.name, FrozenList(types_of_parameters))

        case FGJ.Cast(t, e):
            t0 = TypeExpr(e, Delta, Gamma, CT, Pi)
            if not AUX_T.is_well_formed(t0, Delta, CT):
                raise Exception(f"{e} : {t0}, is not well formed")
            return t

    raise Exception("CANT GO HERE")


def TypeMethod(method_def: FGJ.MethodDef, class_header: FGJ.ClassHeader, Pi: FGJ.Pi, CT: FGJ.ClassTable) -> bool:
    method_sign = Pi[(class_header, method_def.name)][0]
    delta = dict(class_header.bounded_types.items()) | method_sign.gen_typ_ano
    for p in method_sign.gen_typ_ano.values():
        if not AUX_T.is_well_formed(p, delta, CT):
            raise Exception(f"{p} is not well formed")
    for t in method_sign.types_of_arguments:
        if not AUX_T.is_well_formed(t, delta, CT):
            raise Exception(f"{t} is not well formed")
    if not AUX_T.is_well_formed(method_sign.return_type, delta, CT):
        raise Exception(f"{method_sign.return_type} is not well formed")
    gamma = {FGJ.Variable("this"): FGJ.NonTypeVar(class_header.class_name, FrozenList(class_header.bounded_types.keys()))} | {FGJ.Variable(xi): ti for xi, ti in zip(method_def.typed_parameters.keys(), method_sign.types_of_arguments)}
    t0 = TypeExpr(method_def.body, delta, gamma, CT, Pi)
    if not AUX_T.is_subtype(t0, method_sign.return_type, delta, CT):
        raise Exception(f"{t0} is not a subtype of {method_sign.return_type}")
    if not AUX_T.is_valid_method_override(method_def.name, CT[class_header.class_name].superclass, method_sign, CT, Pi):
        raise Exception(f"Invalid override of method {method_def.name} in {class_header.class_name}")
    return True


def TypeClass(class_def: FGJ.ClassDef, CT: FGJ.ClassTable, Pi: FGJ.Pi):
    delta = dict(class_def.generic_type_annotation.items())
    for t in class_def.typed_fields.values():
        if not AUX_T.is_well_formed(t, delta, CT):
            raise Exception(f"{t} is not well formed")
    for n in class_def.generic_type_annotation.values():
        if not AUX_T.is_well_formed(n, delta, CT):
            raise Exception(f"{n} is not well formed")
    if not AUX_T.is_well_formed(class_def.superclass, delta, CT):
        raise Exception(f"{class_def.superclass} is not well formed")
    for method_def in class_def.methods.values():
        TypeMethod(method_def, FGJ.ClassHeader(class_def.name, frozendict(class_def.generic_type_annotation.items())), Pi, CT)
