import FGJ_AST as FGJ

from dataclasses import dataclass


@dataclass(frozen=True)
class TypeVarA(FGJ.Type):
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class SubTypeC:
    """
    t1 < t2
    """
    t1: FGJ.Type
    t2: FGJ.Type

    def __str__(self) -> str:
        return f"{self.t1} <= {self.t2}"


@dataclass(frozen=True)
class EqualC:
    """
    t1 == t2
    """
    t1: FGJ.Type
    t2: FGJ.Type

    def __str__(self) -> str:
        return f"{self.t1} == {self.t2}"


sc = SubTypeC | EqualC

# oc = set[set[sc]]
oc = frozenset[frozenset[sc]]

c = oc | sc

# C = set[c]
C = frozenset[c]


lambdas = dict[tuple[FGJ.ClassHeader, str], list[FGJ.MethodSign]]

µs = dict[FGJ.Variable, FGJ.Type]

BigPi = lambdas

Teta = tuple[FGJ.Pi, µs]
