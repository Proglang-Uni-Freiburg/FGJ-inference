from dataclasses import dataclass
import FGJ_AST as FGJ


# class TypeA:
#     pass


# @dataclass(frozen=True)
# class TypeVarA(TypeA):
#     name: str


# @dataclass(frozen=True)
# class BoundedTypeVarA(TypeA):
#     name: str


# @dataclass(frozen=True)
# class NonTypeVarA(TypeA):
#     name: str
#     types: list[TypeA]


@dataclass(frozen=True)
class TypeVarA(FGJ.TypeVar):
    pass


@dataclass(frozen=True)
class SubTypeC:
    """
    t1 < t2
    """
    t1: FGJ.Type
    t2: FGJ.Type


@dataclass(frozen=True)
class EqualC:
    """
    t1 == t2
    """
    t1: FGJ.Type
    t2: FGJ.Type


sc = SubTypeC | EqualC

oc = set[set[sc]]

c = oc | sc

C = set[c]


lambdas = dict[tuple[FGJ.ClassHeader, str], set[FGJ.MethodSign]]

µs = dict[FGJ.Variable, FGJ.Type]

BigPi = lambdas

Teta = tuple[FGJ.Pi, µs]
