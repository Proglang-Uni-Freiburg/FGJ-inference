import FGJ_AST as FGJ
import FGJ_GT_AST as FGJ_GT

from FGJ_GT_Type import FJType
from FGJ_GT_Unify import Unify
from FGJ_GT_auxiliary_functions import getTypeSigOf, NoSolutionFound


def TypeInference(Pi: FGJ.Pi, index: int, CT: FGJ.ClassTable) -> FGJ.Pi:

    class_def_list = list(CT.values())
    if index >= len(class_def_list):
        return Pi

    while True:
        class_def = class_def_list[index]
        ls, constraint = FJType(Pi, class_def, CT)  # constraint generation

        # brings upper bound of type variables from overriden methods in scope
        d = dict()
        for class_header_tupled, method_sign_list in ls.items():
            class_header, _ = class_header_tupled
            if class_header.class_name == class_def.name:
                for method_sign in method_sign_list:
                    d |= method_sign.gen_typ_ano


        unifys = [(sig, ysEps) for sig, ysEps in Unify(constraint, dict(class_def.generic_type_annotation.items()) | d, CT)]  # constraint solving

        if unifys == []:  # No solution found
            raise NoSolutionFound

        for sig, ysEps in unifys:
            try:
                temp_pi = {class_header_method_tuple: [FGJ.MethodSign(getTypeSigOf(method_sign, ysEps | d, sig), [(ai if type(ai) is not FGJ_GT.TypeVarA else sig[ai]) for ai in method_sign.types_of_arguments], method_sign.return_type if type(method_sign.return_type) is not FGJ_GT.TypeVarA else sig[method_sign.return_type]) for method_sign in method_signs] for class_header_method_tuple, method_signs in ls.items() if class_header_method_tuple[0].class_name == class_def.name}

                # Typecheck class dedinition
                # TypeClass(class_def, CT, Pi | temp_pi)

                new_pi = TypeInference(Pi | temp_pi, index + 1, CT)
                return new_pi

            except NoSolutionFound:
                continue


# The purpose of the following funtions is simply debugging.

# def lambdas_to_string(ls: FGJ_GT.lambdas) -> str:
#     return ", ".join(f"({ch}, {m}) -> [{', '.join(str(v) for v in value)}]" for (ch, m), value in ls.items())


# def constraint_set_to_string(C: FGJ_GT.C) -> str:
#     out = []
#     for constraint in C:
#         match constraint:
#             case FGJ_GT.SubTypeC() | FGJ_GT.EqualC():
#                 out.append(str(constraint))
#             case _:
#                 out.append("(" + ", ".join("(" + constraint_set_to_string(con) + ")" for con in constraint) + ")")
#     return ", ".join(out)
