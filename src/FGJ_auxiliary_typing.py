from typing import Optional
import FGJ_AST as FGJ
import FGJ_GT_AST as FGJ_GT

from frozendict import frozendict
from frozenlist import FrozenList


def substitute_typeVar(T: FGJ.Type, X: FGJ.TypeVar, T_old: FGJ.Type) -> FGJ.Type:
    """
    [T/X]Type(S,T,U,V) -> [T/X]TypeVar(X,Y,Z) or [T/X]NonTypeVar(N,P,Q)
    """
    match T_old:
        case FGJ_GT.TypeVarA(_):
            return T_old
        case FGJ.TypeVar(X.name):
            return T
        case FGJ.TypeVar(_):
            return T_old
        case FGJ.NonTypeVar(name, types):
            return FGJ.NonTypeVar(name, FrozenList([substitute_typeVar(T, X, t) for t in types]))
        case _:
            raise Exception(f"Arguments must be either TypeVar or NonTypeVar but is {type(T_old)}")


def substitute_typeVars(Ts: FrozenList[FGJ.Type], Xs: list[FGJ.TypeVar], T_old: FGJ.Type) -> FGJ.Type:
    """
    ['T/'X]Type(S,T,U,V) -> ['T/'X]TypeVar(X,Y,Z) or ['T/'X]NonTypeVar(N,P,Q)
    """
    for t, x in zip(Ts, Xs):
        T_old = substitute_typeVar(t, x, T_old)
    return T_old


def is_subtype(t1: FGJ.Type, t2: FGJ.Type, Delta: FGJ.Delta, CT: FGJ.ClassTable) -> bool:
    match (t1, t2):
        case (_, FGJ.NonTypeVar("Object", _)):
            return True
        case (FGJ.NonTypeVar("Object", _), _):
            return False
        case (FGJ.Type(), FGJ.Type()) if t1 == t2:
            return True
        case (FGJ.TypeVar(_), _):
            return is_subtype(Delta[t1], t2, Delta, CT)
        case (FGJ.NonTypeVar(t1_name, t1s), FGJ.NonTypeVar(_, _)):
            class_def = CT[t1_name]
            xs = list(class_def.generic_type_annotation.keys())
            n = class_def.superclass
            return is_subtype(substitute_typeVars(t1s, xs, n), t2, Delta, CT)
        case _:
            return False


# only used in typing (type check)
def is_well_formed(t: FGJ.Type, Delta: FGJ.Delta, CT: FGJ.ClassTable) -> bool:
    match t:
        case FGJ.NonTypeVar("Object", _):
            return True
        case FGJ.TypeVar(_):
            return t in Delta.keys()
        case FGJ.NonTypeVar(name, ts):
            # recursivley checking all Types in ts
            are_types_well_formed = all(is_well_formed(type, Delta, CT) for type in ts)
            # pair types in ts and types in ns together
            class_def = CT[name]
            mapped = zip(class_def.generic_type_annotation.values(), ts)
            xs = list(class_def.generic_type_annotation.keys())
            are_types_subtypes = all(is_subtype(ti, substitute_typeVars(ts, xs, ni), Delta, CT) for (ni, ti) in mapped)
            return are_types_well_formed and are_types_subtypes
        case _:
            raise Exception("Type must either be TypeVar or NonTypeVar but is Type")


def fields(t: FGJ.NonTypeVar, CT: FGJ.ClassTable) -> dict[str, FGJ.Type]:
    match t:
        case FGJ.NonTypeVar("Object", _):
            return dict()
        case FGJ.NonTypeVar(name, ts):
            class_def = CT[name]
            typed_fields = class_def.typed_fields.items()
            xs = list(class_def.generic_type_annotation.keys())
            subted_typed_fields = {field: substitute_typeVars(ts, xs, t) for field, t in typed_fields}
            super_class = class_def.superclass
            subted = substitute_typeVars(ts, xs, super_class)
            if type(subted) is not FGJ.NonTypeVar:
                raise Exception("CANT GO HERE - BUT TYPECHECKING")
            return fields(subted, CT) | subted_typed_fields


def mtype(method_name: str, c: FGJ.NonTypeVar, CT: FGJ.ClassTable, PI: FGJ.Pi) -> Optional[FGJ.MethodSign]:
    match c:
        case FGJ.NonTypeVar("Object", _):
            return None
        case FGJ.NonTypeVar(name, ts) if method_name in CT[name].methods.keys():
            class_def = CT[name]
            gen_type_ano = class_def.generic_type_annotation
            method_signature = list(PI[(FGJ.ClassHeader(class_def.name, frozendict(gen_type_ano.items())), method_name)])[0] # Why Set? Get a random ano? ???
            xs = list(gen_type_ano.keys())
            # subted_gen_type_ano: dict[FGJ.TypeVar, FGJ.NonTypeVar] = {sub(ts, xs, yi): sub(ts, xs, pi) for yi, pi in method_signature.gen_typ_ano.items()}
            subted_gen_type_ano: dict[FGJ.TypeVar, FGJ.NonTypeVar] = {yi: substitute_typeVars(ts, xs, pi) for yi, pi in method_signature.gen_typ_ano.items()}
            subted_arguments = [substitute_typeVars(ts, xs, ui) for ui in method_signature.types_of_arguments]
            subted_return_type = substitute_typeVars(ts, xs, method_signature.return_type)
            return FGJ.MethodSign(subted_gen_type_ano, subted_arguments, subted_return_type)

        case FGJ.NonTypeVar(name, ts):
            class_def = CT[name]
            xs = list(class_def.generic_type_annotation.keys())
            subted = substitute_typeVars(ts, xs, class_def.superclass)
            if type(subted) is not FGJ.NonTypeVar:
                raise Exception("CANT GO HERE - BUT TYPECHECKER")
            return mtype(method_name, subted, CT, PI)


# only used in typing (type check)
def is_valid_method_override(method_name: str, n: FGJ.NonTypeVar, method_sign_lower: FGJ.MethodSign, CT: FGJ.ClassTable, PI: FGJ.Pi) -> bool:
    method_sign_upper = mtype(method_name, n, CT, PI)
    if not method_sign_upper:
        return True
    ps = list(method_sign_lower.gen_typ_ano.values())
    qs = list(method_sign_upper.gen_typ_ano.values())
    ysTV = list(method_sign_lower.gen_typ_ano.keys())
    ys: FrozenList[FGJ.Type] = FrozenList(method_sign_lower.gen_typ_ano.keys())
    zs = list(method_sign_upper.gen_typ_ano.keys())
    ts = method_sign_lower.types_of_arguments
    us = method_sign_upper.types_of_arguments
    t0 = method_sign_lower.return_type
    u0 = method_sign_upper.return_type
    ps_equals_qs = all([pi == substitute_typeVars(ys, zs, qi) for pi, qi in zip(ps, qs)])
    ts_equals_us = all([pi == substitute_typeVars(ys, zs, qi) for pi, qi in zip(ts, us)])
    Delta = {yi: pi for yi, pi in zip(ysTV, ps)}
    t0_sub_u0 = is_subtype(t0, substitute_typeVars(ys, zs, u0), Delta, CT)
    return ps_equals_qs and ts_equals_us and t0_sub_u0


# only used in typing (type check)
def bound(n: FGJ.Type, Delta: FGJ.Delta) -> FGJ.NonTypeVar:
    match n:
        case FGJ.TypeVar(_):
            return Delta[n]
        case FGJ.NonTypeVar(_, _):
            return n
        case _:
            raise Exception("CANT GO HERE - BUT TYPECHECKER")


# unused
def is_valid_downcast(c1: FGJ.NonTypeVar, c2: FGJ.NonTypeVar, CT: FGJ.ClassTable) -> bool:
    match c1, c2:
        case FGJ.NonTypeVar("Object", _), FGJ.NonTypeVar("Object", _):
            return True
        case _, FGJ.NonTypeVar("Object", _):
            return list(CT[c1.name].generic_type_annotation.keys()) == []
        case FGJ.NonTypeVar("Object", _), _:
            return False
        case _, _ if CT[c1.name].superclass == c2:
            return list(CT[c1.name].generic_type_annotation.keys()) == CT[c1.name].superclass.types
        case _, _:
            return is_valid_downcast(c1, CT[c1.name].superclass, CT) and is_valid_downcast(CT[c1.name].superclass, c2, CT)
