import FGJ_AST as FGJ
import FGJ_GT_AST as FGJ_GT
import FGJ_auxiliary_typing as AUX
import FGJ_GT_auxiliary_functions as AUX_GT

from frozenlist import FrozenList


def exhaustivelyFig1617(C_prime: set[FGJ_GT.sc], env: FGJ.Delta, CT: FGJ.ClassTable) -> set[FGJ_GT.sc]:
    # step 1
    changed = True
    newC_prime: set[FGJ_GT.sc] = set()
    while changed:
        changed = False
        newC_prime = C_prime.copy()
        for constraint in C_prime:
            match constraint:
                # 1 Argument

                # adapt
                case FGJ_GT.SubTypeC(FGJ.NonTypeVar(n1, ts), FGJ.NonTypeVar(n2, us)) if AUX_GT.isSubtypeByName(n1, n2, CT):
                    xs: FrozenList[FGJ.Type] = FrozenList([FGJ.TypeVar("x" + str(i)) for i, _ in enumerate(ts)])
                    ns = AUX_GT.genericSupertype(n1, xs, n2, env, CT)
                    newC_prime.remove(constraint)
                    subtedns = FrozenList([AUX.sub(ts, xs, ni) for ni in ns])
                    newC_prime.add(FGJ_GT.EqualC(FGJ.NonTypeVar(n2, subtedns), FGJ.NonTypeVar(n2, us)))
                    changed = True

                # # is this implied by the example 8 or not?
                # case FGJ_GT.SubTypeC(FGJ.TypeVar(n1), FGJ.NonTypeVar(n2, us)) if not isinstance(constraint.t1, FGJ_GT.TypeVarA) and AUX_GT.isSubtypeByName(env[FGJ.TypeVar(n1)].name, n2, CT):
                #     ns = AUX_GT.genericSupertype(env[FGJ.TypeVar(n1)].name, env[FGJ.TypeVar(n1)].types, n2, CT)
                #     newC_prime.remove(constraint)
                #     newC_prime.add(FGJ_GT.EqualC(FGJ.NonTypeVar(n2, ns), FGJ.NonTypeVar(n2, us)))
                #     changed = True

                # reduce
                case FGJ_GT.EqualC(FGJ.NonTypeVar(c, ts), FGJ.NonTypeVar(d, us)) if c == d:
                    newC_prime.remove(constraint)
                    for ti, ui in zip(ts, us):
                        newC_prime.add(FGJ_GT.EqualC(ti, ui))
                    changed = True

                # equals
                case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b)):
                    equals: list[FGJ_GT.SubTypeC] = AUX_GT.findCircle(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b), C_prime)
                    for sc in equals:
                        newC_prime.remove(sc)
                        newC_prime.add(FGJ_GT.EqualC(sc.t1, sc.t2))
                        changed = True

                # erase
                case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b)) if a == b:
                    newC_prime.remove(constraint)
                    changed = True

                # # X = X redundant
                # case FGJ_GT.EqualC(FGJ.TypeVar(x), FGJ.TypeVar(z)) if x == z:
                #     newC_prime.remove(constraint)
                #     changed = True

                # swap
                case FGJ_GT.EqualC(FGJ.NonTypeVar(n, ts), FGJ_GT.TypeVarA(a)):
                    newC_prime.remove(constraint)
                    newC_prime.add(FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(n, ts)))
                    changed = True

                # # swap X = a -> a = X? redundant
                # case FGJ_GT.EqualC(FGJ.TypeVar(n), FGJ_GT.TypeVarA(a)):
                #     newC_prime.remove(constraint)
                #     newC_prime.add(FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ.TypeVar(n)))
                #     changed = True

                # 2 Arguments
            for constraint2 in C_prime:
                if constraint == constraint2:
                    continue

                match constraint, constraint2:

                    # match
                    case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(c, _)), FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(d, _)) if a == b:
                        if AUX_GT.isSubtypeByName(c, d, CT):
                            newC_prime.remove(constraint2)
                            newC_prime.add(FGJ_GT.SubTypeC(constraint.t2, constraint2.t2))
                            changed = True
                        elif AUX_GT.isSubtypeByName(d, c, CT):
                            newC_prime.remove(constraint)
                            newC_prime.add(FGJ_GT.SubTypeC(constraint2.t2, constraint.t2))
                            changed = True

                    # match reverse (own)
                    case FGJ_GT.SubTypeC(FGJ_GT.FGJ.NonTypeVar(c, _), FGJ_GT.TypeVarA(a)), FGJ_GT.SubTypeC(FGJ.NonTypeVar(d, _), FGJ_GT.TypeVarA(b)) if a == b:
                        if AUX_GT.isSubtypeByName(c, d, CT):
                            newC_prime.remove(constraint)
                            newC_prime.add(FGJ_GT.SubTypeC(constraint.t1, constraint2.t1))
                            changed = True
                        elif AUX_GT.isSubtypeByName(d, c, CT):
                            newC_prime.remove(constraint2)
                            newC_prime.add(FGJ_GT.SubTypeC(constraint2.t1, constraint.t1))
                            changed = True

                    # adopt
                    case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(c, cs)), FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(d, _)) if AUX_GT.isConnected(FGJ_GT.TypeVarA(b), FGJ_GT.TypeVarA(a), C_prime):
                        new_constraint = FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(c, cs))
                        if newC_prime.isdisjoint({new_constraint}):
                            newC_prime.add(new_constraint)
                            changed = True

                    # adopt reverse (own)
                    case FGJ_GT.SubTypeC(FGJ.NonTypeVar(c, cs), FGJ_GT.TypeVarA(a)), FGJ_GT.SubTypeC(FGJ.NonTypeVar(d, _), FGJ_GT.TypeVarA(b)) if AUX_GT.isConnected(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b), C_prime):
                        newC_prime.add(FGJ_GT.SubTypeC(FGJ.NonTypeVar(c, cs), FGJ_GT.TypeVarA(b)))
                        changed = True

        C_prime = newC_prime
    return newC_prime


# TESTING
def constraint_set_to_string(C: FGJ_GT.C) -> str:
    out = []
    for constraint in C:
        match constraint:
            case FGJ_GT.SubTypeC() | FGJ_GT.EqualC():
                out.append(str(constraint))
            case _:
                out.append("(" + ", ".join("(" + constraint_set_to_string(con) + ")" for con in constraint) + ")")
    return ", ".join(out)
# END


def Unify(C: FGJ_GT.C, env: FGJ.Delta, CT: FGJ.ClassTable) -> tuple[dict[FGJ.Type, FGJ.Type], FGJ.GenTypeAno]:
    #                        -//-                          -> tuple[dict[FGJ_GT.TypeVarA, FGJ.Type], FGJ.GenTypeAno]:
    for C_prime in AUX_GT.gen_C_prime(C):

        # X -> X<>
        newC_prime = set()
        for c in C_prime:
            match c:
                case FGJ_GT.EqualC(t1, t2):
                    if type(t1) is FGJ.TypeVar:
                        t1 = FGJ.NonTypeVar(t1.name, FrozenList())
                    if type(t2) is FGJ.TypeVar:
                        t2 = FGJ.NonTypeVar(t2.name, FrozenList())
                    newC_prime.add(FGJ_GT.EqualC(t1, t2))
                case FGJ_GT.SubTypeC(t1, t2):
                    if type(t1) is FGJ.TypeVar:
                        t1 = FGJ.NonTypeVar(t1.name, FrozenList())
                    if type(t2) is FGJ.TypeVar:
                        t2 = FGJ.NonTypeVar(t2.name, FrozenList())
                    newC_prime.add(FGJ_GT.SubTypeC(t1, t2))
        C_prime = newC_prime

        C_prime = exhaustivelyFig1617(C_prime, env, CT)

        # step 2
        noSolution = False
        lowerupperBs: list[tuple[FGJ_GT.SubTypeC, FGJ_GT.SubTypeC]] = list()
        removeLater: set[FGJ_GT.SubTypeC] = set()
        newC_prime = C_prime.copy()
        for constraint in C_prime:
            # skip step 2 if C_prime is already in solved form
            if AUX_GT.is_solved_form(C_prime):
                break

            match constraint:
                # 1 Argument
                # Own C<Ts> = D<Us> -> No solution
                case FGJ_GT.EqualC(FGJ.NonTypeVar(c, _), FGJ.NonTypeVar(d, _)) if d != c:
                    noSolution = True
                    break

                # 1
                case FGJ_GT.SubTypeC(FGJ.NonTypeVar(c, _), FGJ.NonTypeVar(d, _)) if not AUX_GT.isSubtypeByName(c, d, CT):
                    noSolution = True
                    break

                # 3
                case FGJ_GT.SubTypeC(FGJ.NonTypeVar(c, _), FGJ_GT.TypeVarA(b)):
                    # adding or constraints to c_prime
                    upperC = FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar("Object", FrozenList()))
                    # finfing upperbound constraint
                    for con in C_prime:
                        match con:
                            case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(d, _)):
                                upperC = con
                                newC_prime.remove(con)
                                break
                    lowerupperBs.append((constraint, upperC))
                    newC_prime.remove(constraint)
                    new_constraint = FGJ_GT.SubTypeC(constraint.t1, upperC.t2)
                    newC_prime.add(new_constraint)
                    # do we need to remove them later or are they removed by the rules of 16/17?
                    removeLater.add(new_constraint)

            # 2 Arguments
            # 2
            # early break if no solution is possible in this constraint set (C_prime)
            if noSolution:
                break

            for constraint2 in C_prime:
                if constraint == constraint2:
                    continue

                match constraint, constraint2:
                    case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(c, _)), FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(d, _)) if a == b and not AUX_GT.isSubtypeByName(c, d, CT) and not AUX_GT.isSubtypeByName(d, c, CT):
                        noSolution = True
                        break

            # early break if no solution is possible in this constraint set (C_prime)
            if noSolution:
                break

        C_prime = newC_prime

        # skip to next C_prime because the current has no solution
        if noSolution:
            continue

        # solving expandLB
        for lowerC, upperC in lowerupperBs:
            cts = lowerC.t1
            dts = upperC.t2
            if type(cts) is not FGJ.NonTypeVar or type(dts) is not FGJ.NonTypeVar:
                raise Exception("CANT GO HERE - BUT TYPECHECKER")
            xs = FrozenList(FGJ.TypeVar("x" + str(i)) for i, _ in enumerate(cts.types))
            ns = AUX_GT.genericSupertypeList(cts.name, xs, dts.name, env, CT)
            C_prime |= {frozenset(frozenset([FGJ_GT.EqualC(lowerC.t2, AUX.sub(cts.types, xs, ni))]) for ni in ns)}

        C_prime = exhaustivelyFig1617(C_prime, env, CT)
        # remove the constraint previously added
        C_prime = C_prime.difference(removeLater)

        # step 3
        for C_prime2 in AUX_GT.gen_C_prime(C_prime):
            noSolution = False

            changed = False
            changing = True
            while changing:
                changing = False

                if noSolution:
                    break

                # subst
                for constraint in C_prime2:
                    match constraint:
                        case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), t):
                            if AUX_GT.occoursIn(FGJ_GT.TypeVarA(a), t):
                                noSolution = True
                                break
                            temp_C2 = C_prime2.copy()
                            temp_C2.remove(constraint)
                            newTempC2 = AUX_GT.subConstraint(t, FGJ_GT.TypeVarA(a), temp_C2)
                            if newTempC2.difference(temp_C2):
                                newTempC2.add(constraint)
                                C_prime2 = newTempC2
                                changing = True
                                changed = True
                                break

            # skip this C_prime2 because it has no solution
            if noSolution:
                continue

            # step 4
            if changed:
                # can we just return here? Should be fine
                return Unify(C_prime2, env, CT)
            if not AUX_GT.is_solved_form(C_prime2):
                raise Exception("NOT IN SOLVED FORM: " + constraint_set_to_string(C_prime2))

            # step 5
            # not sure if we can do both rules in one for-loop since sub may produce a case fpr elim
            newTempC2 = C_prime2.copy()
            for constraint in C_prime2:
                match constraint:
                    # is this exhaustively
                    case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b)):
                        newTempC2.remove(constraint)
                        newTempC2 = AUX_GT.subConstraint(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b), newTempC2)
                        newTempC2.add(FGJ_GT.EqualC(FGJ_GT.TypeVarA(b), FGJ_GT.TypeVarA(a)))

            C_prime2 = newTempC2.copy()

            for constraint in C_prime2:
                match constraint:
                    case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b)) if a == b:
                        newTempC2.remove(constraint)

            C_prime2 = newTempC2

            # step 6
            C_equal: set[FGJ_GT.EqualC] = set()
            C_sub: set[FGJ_GT.SubTypeC] = set()

            for constraint in C_prime2:
                match constraint:
                    case FGJ_GT.EqualC(_):
                        C_equal.add(constraint)
                    case FGJ_GT.SubTypeC(_):
                        C_sub.add(constraint)

            ass: list[FGJ_GT.TypeVarA] = list({c.t1 for c in C_sub if type(c.t1) is FGJ_GT.TypeVarA})

            # 'Z' is not allowed to occur already, do a check here or search for another
            start = "Z"
            Z_fresh = FGJ.TypeVar(start)
            Zs_fresh = [FGJ.TypeVar(start + str(i)) for i, _ in enumerate(ass)]
            # why only X in C_sub? why not all T?
            print("Eq:", constraint_set_to_string(C_equal))
            print("Sub:", constraint_set_to_string(C_sub))
            print(ass)
            print(Zs_fresh)
            o = {ai: zi for ai, zi in zip(ass, Zs_fresh)} | {c.t1: AUX_GT.sub(Zs_fresh, ass, c.t2) for c in C_equal} | {c.t1: c.t2 for c in C_sub if type(c.t2) is FGJ.TypeVar}
            for k, v in o.items():
                print(f"o[{k}] = {v}")
            # all c from C_sub?
            y: dict[FGJ.TypeVar, FGJ.NonTypeVar] = {Z_fresh: AUX_GT.sub(Zs_fresh, ass, c.t2) for c in C_sub if type(c.t2) if FGJ.NonTypeVar}
            return o, y

    raise Exception("NO SOLUTION FOUND")
