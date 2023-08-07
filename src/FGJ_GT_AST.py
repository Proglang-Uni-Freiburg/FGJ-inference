import FGJ_AST as FGJ

from dataclasses import dataclass
from hset import hSet


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

# oc = set[set[sc]]
oc = hSet[hSet[sc]]

c = oc | sc

# C = set[c]
C = hSet[c]


lambdas = dict[tuple[FGJ.ClassHeader, str], set[FGJ.MethodSign]]

µs = dict[FGJ.Variable, FGJ.Type]

BigPi = lambdas

Teta = tuple[FGJ.Pi, µs]
