from dataclasses import dataclass
import FGJ_AST as FGJ


class TypeA:
    pass


@dataclass(frozen=True)
class TypeVarA(TypeA):
    name: str


@dataclass(frozen=True)
class BoundedTypeVarA(TypeA):
    name: str


@dataclass(frozen=True)
class NonTypeVarA(TypeA):
    name: str
    types: list[TypeA]


@dataclass(frozen=True)
class SubTypeC:
    """
    t1 < t2
    """
    t1: TypeA
    t2: TypeA


@dataclass(frozen=True)
class EqualC:
    """
    t1 == t2
    """
    t1: TypeA
    t2: TypeA


sc = SubTypeC | EqualC

oc = set[set[sc]]

c = oc | sc

C = set[c]


@dataclass(frozen=True)
class ClassHeaderA:
    class_name: str
    bounded_types: dict[BoundedTypeVarA, NonTypeVarA]


@dataclass(frozen=True)
class MethodSignA:
    bounded_types: dict[BoundedTypeVarA, NonTypeVarA]
    types_of_arguments: list[TypeA]
    return_type: TypeA


lambdas = dict[tuple[ClassHeaderA, str], MethodSignA]

µs = dict[FGJ.Variable, TypeA]

BigPi: lambdas

Teta = tuple[FGJ.Pi, µs]
