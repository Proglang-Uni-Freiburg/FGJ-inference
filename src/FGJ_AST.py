from dataclasses import dataclass
from frozendict import frozendict
from frozenlist import FrozenList


@dataclass(frozen=True)
class Type:
    pass


@dataclass(frozen=True)
class NonTypeVar(Type):
    name: str
    types: FrozenList['Type']

    def __post_init__(self):
        self.types.freeze()

    def __str__(self):
        return self.name + "<" + ', '.join(str(t) for t in self.types) + ">"


@dataclass(frozen=True)
class TypeVar(Type):
    name: str

    def __str__(self):
        return self.name


GenTypeAno = dict[TypeVar, NonTypeVar]


FieldEnv = dict[str, Type]


@dataclass(frozen=True)
class Expression:
    pass


@dataclass(frozen=True)
class Variable(Expression):
    name: str

    def __str__(self):
        return self.name


@dataclass(frozen=True)
class FieldLookup(Expression):
    expression: Expression
    field_name: str

    def __str__(self) -> str:
        expr = "(" + str(self.expression) + ")" if isinstance(self.expression, Cast) else str(self.expression)
        return f"{expr}.{self.field_name}"


@dataclass(frozen=True)
class MethodLookup(Expression):
    expression: Expression
    list_of_types: list[Type]
    method_name: str
    parameters: list[Expression]

    def __str__(self) -> str:
        expr = "(" + str(self.expression) + ")" if isinstance(self.expression, Cast) else str(self.expression)
        types = f"<{', '.join(str(t) for t in self.list_of_types)}>" if self.list_of_types else ""
        return f"{expr}.{self.method_name}{types}({', '.join(str(e) for e in self.parameters)})"


@dataclass(frozen=True)
class NewClass(Expression):
    type: NonTypeVar
    parameters: list[Expression]

    def __str__(self) -> str:
        return f"new {str(self.type.name)}({', '.join(str(e) for e in self.parameters)})"


@dataclass(frozen=True)
class Cast(Expression):
    type: NonTypeVar
    expression: Expression

    def __str__(self) -> str:
        return f"({str(self.type)}){str(self.expression)}"


ParaEnv = dict[str, Type]


@dataclass(frozen=True)
class MethodDef:
    generic_type_annotation: GenTypeAno
    return_type: Type | None
    typed_parameters: ParaEnv
    name: str
    body: Expression

    def __str__(self) -> str:
        gta = "<" + ", ".join(f"{k} extends {v}" for k, v in self.generic_type_annotation.items()) + "> " if self.generic_type_annotation else ""
        ret = str(self.return_type) + " " if self.return_type else ""
        out = f"{gta}{ret}{self.name}("
        out += ', '.join(f'{str(argument_type) + " " if argument_type else ""}{argument_name}' for argument_name, argument_type in self.typed_parameters.items())
        out += ") {\n\treturn " + str(self.body) + ";\n}"
        return out


@dataclass(frozen=True)
class ClassDef:
    name: str
    generic_type_annotation: GenTypeAno
    superclass: NonTypeVar
    typed_fields: FieldEnv
    methods: dict[str, MethodDef]

    def __str__(self) -> str:
        """
        Without Constructor
        """
        gta = "<" + ", ".join(f"{x} extends {y}" for x, y in self.generic_type_annotation.items()) + ">" if self.generic_type_annotation else ""
        out = f"class {self.name}{gta} extends {str(self.superclass)}" + " {"
        if self.typed_fields or self.methods:
            out += "\n"
        out += '\n'.join(f'\t{field_type} {field_name};' for field_name, field_type in self.typed_fields.items())
        if self.typed_fields:
            out += "\n"
        out += '\n'.join("\n".join(['\t' + line for line in str(method_def).split("\n")]) for method_def in self.methods.values())
        if self.methods:
            out += "\n"
        return out + "}"


@dataclass(frozen=True)
class ClassHeader:
    class_name: str
    bounded_types: frozendict[TypeVar, NonTypeVar]

    def __str__(self) -> str:
        return f"{self.class_name}<{', '.join(f'{v}: {n}' for v, n in self.bounded_types.items())}>"


@dataclass(frozen=True)
class MethodSign:
    gen_typ_ano: GenTypeAno
    types_of_arguments: list[Type]
    return_type: Type

    def __str__(self) -> str:
        return f"<{', '.join(f'{k} extends {v}' for k, v in self.gen_typ_ano.items())}>[{', '.join(str(arg) for arg in self.types_of_arguments)}] -> {self.return_type}"


Pi = dict[tuple[ClassHeader, str], list[MethodSign]]

Delta = dict[TypeVar, NonTypeVar]
Env = dict[Variable, Type]
ClassTable = dict[str, ClassDef]


@dataclass(frozen=True)
class Program:
    CT: ClassTable
    expression: Expression

    def __str__(self) -> str:
        out = '\n\n'.join([str(class_def) for class_def in self.CT.values()])
        return out + f"\n\n{str(self.expression)}"
