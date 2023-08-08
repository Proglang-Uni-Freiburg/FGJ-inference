from lark import Lark
from lark import Transformer

from frozenlist import FrozenList

import FGJ_AST as FGJ


featherweight_gerneric_java_parser = Lark(r"""

    %import common.WS
    %ignore WS



    identifier : /[a-zA-Z]\w*/

    type_var : identifier

    type_list : type ("," type)*

    non_type_var : identifier "<" type_list? ">"

    type : non_type_var | type_var

    cast : "(" non_type_var ")" expression

    variable : identifier

    field_lookup : expression "." identifier

    method_lookup : expression ("<" type_list ">")? "." identifier "(" list_of_exprs ")"

    new_class : "new " identifier("<" type_list ">")? "(" list_of_exprs ")"

    expression : "(" expression ")" | cast | variable | field_lookup | method_lookup | new_class

    list_of_exprs : (expression ("," expression)*)?


    gen_type_ano_helper : type_var " extends " non_type_var

    gen_type_ano : "<" (gen_type_ano_helper ("," gen_type_ano_helper)*)? ">"


    fieldenv_helper : type " " identifier

    fieldenv : (fieldenv_helper ";")*


    varenv_helper : type " " identifier

    varenv : (varenv_helper ("," varenv_helper)*)?


    list_of_idents : (identifier ("," identifier)*)?

    constructor : identifier "(" list_of_idents ")" "{" "super(" list_of_idents "); " ("this." identifier "=" identifier ";")* "}"


    method_list : method_def*

    method_def : (gen_type_ano type)? identifier "(" (varenv | list_of_idents) ")" "{" "return " expression ";" "}"


    class_def : "class " identifier gen_type_ano? " extends " non_type_var "{" fieldenv method_list "}"

    class_table : class_def*

    program : class_table (" " | "\n") expression

    """, start=["identifier", "type_var", "non_type_var", "type", "type_list", "cast", "variable", "field_lookup", "method_lookup", "new_class", "expression", "list_of_exprs", "gen_type_ano", "gen_type_ano_helper", "fieldenv", "fieldenv_helper", "list_of_idents", "constructor", "method_list", "method_def", "class_def", "class_table", "program"]
    )


class TreeToFGJ(Transformer):
    def identifier(self, list_of_chars):
        identifier = "".join(list_of_chars)
        return identifier

    def type(self, tt):
        (t,) = tt
        return t

    def type_list(self, tl):
        return tl

    def type_var(self, tv):
        (name,) = tv
        return FGJ.TypeVar(name)

    def non_type_var(self, tntv):
        match len(tntv):
            case 2:
                name, types = tntv
                types = FrozenList(types)
            case _:
                (name,) = tntv
                types = FrozenList()
        return FGJ.NonTypeVar(name, types)

    def cast(self, tc):
        type, expression = tc
        return FGJ.Cast(type, expression)

    def variable(self, tv):
        (name,) = tv
        return FGJ.Variable(name)

    def field_lookup(self, tf):
        expression, name = tf
        return FGJ.FieldLookup(expression, name)

    def method_lookup(self, tm):
        match len(tm):
            case 4:
                expression, list_of_types, method_name, parameters = tm
            case _:
                expression, method_name, parameters, = tm
                list_of_types = list()
        return FGJ.MethodLookup(expression, list_of_types, method_name, parameters)

    def new_class(self, tc):
        match len(tc):
            case 3:
                name, list_of_types, parameters = tc
                list_of_types = FrozenList(list_of_types)
            case 2:
                name, parameters = tc
                list_of_types = FrozenList()
        return FGJ.NewClass(FGJ.NonTypeVar(name, list_of_types), parameters)

    def expression(self, te):
        (e,) = te
        return e

    def list_of_exprs(self, le):
        return le

    def gen_type_ano_helper(self, tgtah):
        type_var, non_type_var = tgtah
        return type_var, non_type_var

    def gen_type_ano(self, tgta):
        return dict(tgta)

    def fieldenv_helper(self, tfh):
        type, identifier = tfh
        return identifier, type

    def fieldenv(self, f):
        return dict(f)

    def varenv_helper(self, tvh):
        type, identifier = tvh
        return identifier, type

    def varenv(self, v):
        return dict(v)

    def list_of_idents(self, tl):
        return tl

    def method_def(self, tmd):
        match len(tmd):
            case 5:
                gta, return_type, name, parameters, body = tmd
            case _:
                name, parameters, body = tmd
                gta = dict()
                return_type = None
        if type(parameters) == list:
            parameters = dict(map(lambda x: (x, None), parameters))
        return FGJ.MethodDef(gta, return_type, parameters, name, body)

    def method_list(self, ml):
        return {m.name: m for m in ml}

    def class_def(self, tcd):
        match len(tcd):
            case 5:
                name, gta, superclass_type, typed_fields, method_list = tcd
            case _:
                name, superclass_type, typed_fields, method_list = tcd
                gta = dict()
        if type(typed_fields) == list:
            typed_fields = {name: None for name in typed_fields}
        return FGJ.ClassDef(name, gta, superclass_type, typed_fields, method_list)

    def class_table(selc, ct):
        return {c.name: c for c in ct}

    def program(self, tp):
        ct, e = tp
        return FGJ.Program(ct, e)


def fgj_parse(source_code_txt: str, start_rule: str = "program") -> FGJ.Program:
    '''
    Parses a given program source code textfile to a Featherweight Generic Java program
    ( A program is a pair of a classtable and an expression )
    '''
    tree = featherweight_gerneric_java_parser.parse(source_code_txt, start_rule)
    shaped_tree = TreeToFGJ().transform(tree)
    return shaped_tree
