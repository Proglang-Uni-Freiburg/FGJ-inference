import FGJ_AST as FGJ
import FGJ_GT_AST as FGJ_GT

from FGJ_GT_Type import FJType
from FGJ_GT_Unify import Unify
from frozendict import frozendict
from FGJ_GT_auxiliary_functions import getTypeSigOf, NoSolutionFound


def TypeInference(Pi: FGJ.Pi, index: int, CT: FGJ.ClassTable) -> FGJ.Pi:
    print("INDEX:", index)
    class_def_list = list(CT.values())
    if index >= len(class_def_list):
        return Pi
    while index >= 0:
        class_def = class_def_list[index]
        ls, constraint = FJType(Pi, class_def, CT)  # constraint generation
        print("Pi:")
        for ms in Pi.values():
            print(ms)
        print("constraints:", constraint_set_to_string(constraint))
        unifys = [(sig, ysEps) for sig, ysEps in Unify(constraint, dict(class_def.generic_type_annotation.items()), CT)]  # constraint solving
        for sig, ysEps in unifys:
            try:
                # set or single? (set(MethodSign))
                # new_pi = TypeInference(Pi | {class_header_method_tuple: [FGJ.MethodSign({yi: ni for yi, ni in ysEps.items() if yi in [sig[ai] for ai in method_sign.types_of_arguments]}, [sig[ai] for ai in method_sign.types_of_arguments], sig[method_sign.return_type]) for method_sign in method_signs] for class_header_method_tuple, method_signs in ls.items() if method_signs not in Pi.values()}, index + 1, CT)
                new_pi = TypeInference(Pi | {class_header_method_tuple: [FGJ.MethodSign(getTypeSigOf(method_sign, ysEps, sig), [sig[ai] for ai in method_sign.types_of_arguments], sig[method_sign.return_type]) for method_sign in method_signs] for class_header_method_tuple, method_signs in ls.items() if method_signs not in Pi.values()}, index + 1, CT)
                return new_pi
            except NoSolutionFound:
                print("AUA")
                continue
        raise Exception("UNREACHABLE")  # ...
    raise NoSolutionFound


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
                out.append("(" + ", ".join("(" + constraint_set_to_string(con) + ")" for con in constraint) + ")")
    return ", ".join(out)


if __name__ == "__main__":
    # testing

    from FGJ_run import read_from


    program = read_from("src\example_code.featherweight.java")
    # print(program.CT)

    # print(program.CT)

    # lambdas, c = FJType(dict(), program.CT["Pair"], program.CT)

    # print("LAMBDAS:\n", lambdas_to_string(lambdas))
    # print("C:\n", constraint_set_to_string(c))

    # o, ysps = Unify(c, dict(program.CT["Pair"].generic_type_annotation), program.CT)

    # print("o:")
    # for k, v in o.items():
    #     print(f"{k}: {v}")

    # for (ch, n), ms in lambdas.items():
    #     print(ch, n, ":")
    #     # print(ms)
    #     for m in ms:
    #         print("\t", m)
    #         print("\t", FGJ.MethodSign(ysps, [o[a] for a in m.types_of_arguments], o[m.return_type]))


    d = TypeInference(dict(), 0, program.CT)

    for (ch, m), mss in d.items():
        print(ch, m, ":")
        for ms in mss:
            print(ms)
