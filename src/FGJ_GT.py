import FGJ_AST as FGJ

from FGJ_GT_Type import FJType
from FGJ_GT_Unify import Unify


def TypeInference(Pi: FGJ.Pi, class_def: FGJ.ClassDef, CT: FGJ.ClassTable) -> FGJ.Pi:
    ls, constraint = FJType(Pi, class_def, CT)  # constraint generation
    sig, ysEps = Unify(constraint, class_def.generic_type_annotation, CT)  # constraint solving
    # set or single? (set(MethodSign))
    return Pi | {class_header_method_tuple: frozenset(FGJ.MethodSign(ysEps, [sig[ai] for ai in method_sign.types_of_arguments], sig(method_sign.return_type))) for class_header_method_tuple, method_sign in ls.items()}


# testing

from FGJ_run import read_from


program = read_from("src\example_code.txt")

# print(program.CT)

print(FJType(dict(), program.CT["Pair"], program.CT))

# print(TypeInference(dict(), class_def, CT))
