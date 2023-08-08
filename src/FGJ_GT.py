import FGJ_AST as FGJ
import FGJ_GT_AST as FGJ_GT

from FGJ_GT_Type import FJType, TypeExpr
from FGJ_GT_Unify import Unify


def TypeInference(Pi: FGJ.Pi, class_def: FGJ.ClassDef, CT: FGJ.ClassTable) -> FGJ.Pi:
    ls, constraint = FJType(Pi, class_def, CT)  # constraint generation
    sig, ysEps = Unify(constraint, dict(class_def.generic_type_annotation.items()), CT)  # constraint solving
    # set or single? (set(MethodSign))
    return Pi | {class_header_method_tuple: [FGJ.MethodSign(ysEps, [sig[ai] for ai in method_sign.types_of_arguments], sig(method_sign.return_type))] for class_header_method_tuple, method_sign in ls.items()}

# to_string methods


def lambdas_to_string(ls: FGJ_GT.lambdas) -> str:
    return ", ".join(f"({ch}, {m}) -> [{', '.join(str(v) for v in value)}]" for (ch, m), value in ls.items())


def constraint_set_to_string(C: FGJ_GT.C) -> str:
    out = []
    for constraint in C:
        match constraint:
            case FGJ_GT.SubTypeC() | FGJ_GT.EqualC():
                out.append(str(constraint))
            case _:
                out.append("(" + ", ".join(constraint_set_to_string(con) for con in constraint) + ")")
    return ", ".join(out)


# testing

from FGJ_run import read_from


program = read_from("src\example_code.txt")
# print(program.CT)

# print(program.CT)

lambdas, c = FJType(dict(), program.CT["Pair"], program.CT)

print("LAMBDAS:\n", lambdas_to_string(lambdas))
print("C:\n", constraint_set_to_string(c))

print(Unify(c, dict(), program.CT))

# print(TypeInference(dict(), class_def, CT))
