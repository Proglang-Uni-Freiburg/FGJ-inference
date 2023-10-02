import FGJ_AST as FGJ
import FGJ_GT_AST as FGJ_GT
import FGJ_auxiliary_typing as AUX
import FGJ_GT_auxiliary_functions as AUX_GT

from frozenlist import FrozenList
from typing import Generator, Any


z_fresh = AUX_GT.freshVar("Z")


def reduceAndAdapt(C_prime: set[FGJ_GT.sc], env: FGJ.Delta, CT: FGJ.ClassTable) -> set[FGJ_GT.sc]:
    """
    Step 1
    Exhaustively applying rules of figure 16 and 17.
    """

    # As long as C_prime changes we try to apply a rule
    changed = True
    newC_prime: set[FGJ_GT.sc] = set()
    while changed:
        changed = False
        newC_prime = C_prime.copy()

        # rules with one argument
        for constraint in C_prime:
            match constraint:
                # adapt
                case FGJ_GT.SubTypeC(FGJ.NonTypeVar(n1, ts), FGJ.NonTypeVar(n2, us)) if AUX_GT.isSubtypeByName(n1, n2, env, CT):
                    xs: FrozenList[FGJ.Type] = FrozenList([FGJ.TypeVar("x" + str(i)) for i, _ in enumerate(ts)])
                    ns = AUX_GT.genericSupertype(n1, xs, n2, env, CT)
                    newC_prime.remove(constraint)
                    subtedns = FrozenList([AUX.substitute_typeVars(ts, xs, ni) for ni in ns])
                    newC_prime.add(FGJ_GT.EqualC(FGJ.NonTypeVar(n2, subtedns), FGJ.NonTypeVar(n2, us)))
                    changed = True

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

                # swap
                case FGJ_GT.EqualC(FGJ.NonTypeVar(n, ts), FGJ_GT.TypeVarA(a)):
                    newC_prime.remove(constraint)
                    newC_prime.add(FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(n, ts)))
                    changed = True

        if changed:
            C_prime = newC_prime
            continue

        # Rules with two arguments
        for constraint in C_prime:

            if changed:
                break

            for constraint2 in C_prime:

                if constraint == constraint2:
                    continue

                match constraint, constraint2:

                    # match
                    case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(c, cs)), FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(d, _)) if a == b:
                        # match <
                        if a == b and AUX_GT.isSubtypeByName(c, d, env, CT):
                            newC_prime.remove(constraint2)
                            newC_prime.add(FGJ_GT.SubTypeC(constraint.t2, constraint2.t2))
                            changed = True
                            break
                        # match >
                        elif a == b and AUX_GT.isSubtypeByName(d, c, env, CT):
                            newC_prime.remove(constraint)
                            newC_prime.add(FGJ_GT.SubTypeC(constraint2.t2, constraint.t2))
                            changed = True
                            break

                    # adopt
                    case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(c, cs)), FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(d, _)) if AUX_GT.isConnected(FGJ_GT.TypeVarA(b), FGJ_GT.TypeVarA(a), C_prime):
                        new_constraint = FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(c, cs))
                        if new_constraint.t2.name == "Object":
                            continue
                        if newC_prime.isdisjoint({new_constraint}):
                            newC_prime.add(new_constraint)
                            changed = True
                            break

                    # match reverse and adopt reverse (own)
                    case FGJ_GT.SubTypeC(FGJ.NonTypeVar(c, cs), FGJ_GT.TypeVarA(a)), FGJ_GT.SubTypeC(FGJ.NonTypeVar(d, _), FGJ_GT.TypeVarA(b)):
                        # match reverse < (own)
                        if a == b and AUX_GT.isSubtypeByName(c, d, env, CT):
                            newC_prime.remove(constraint)
                            newC_prime.add(FGJ_GT.SubTypeC(constraint.t1, constraint2.t1))
                            changed = True
                            break
                        # match reverse > (own)
                        elif a == b and AUX_GT.isSubtypeByName(d, c, env, CT):
                            newC_prime.remove(constraint2)
                            newC_prime.add(FGJ_GT.SubTypeC(constraint2.t1, constraint.t1))
                            changed = True
                            break
                        # adopt reverse (own)
                        elif AUX_GT.isConnected(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b), C_prime):
                            newC_prime.add(FGJ_GT.SubTypeC(FGJ.NonTypeVar(c, cs), FGJ_GT.TypeVarA(b)))
                            changed = True
                            break

        C_prime = newC_prime
    return newC_prime


def Unify(C: FGJ_GT.C, env: FGJ.Delta, CT: FGJ.ClassTable) -> Generator[tuple[dict[FGJ_GT.TypeVarA, FGJ.Type], FGJ.GenTypeAno], Any, None]:
    for C_prime in AUX_GT.gen_C_prime(C):

        # X -> X<>
        C_prime = AUX_GT.TypeVarToNonTypeVar(C_prime)

        # step 1
        C_prime = reduceAndAdapt(C_prime, env, CT)

        # step 2
        noSolution = False
        lowerupperBs: list[tuple[FGJ_GT.SubTypeC, FGJ_GT.SubTypeC, bool]] = list()
        removeLater: set[FGJ_GT.SubTypeC] = set()
        newC_prime = C_prime.copy()
        for constraint in C_prime:
            # even if it is in solved form case 3 can be implied

            match constraint:
                # 1 Argument
                # Own C<Ts> = D<Us> -> No solution -- expandLB(A, B) is A </ B or not?
                case FGJ_GT.EqualC(FGJ.NonTypeVar(c, _), FGJ.NonTypeVar(d, _)) if d != c:
                    noSolution = True
                    break

                # 1
                case FGJ_GT.SubTypeC(FGJ.NonTypeVar(c, _), FGJ.NonTypeVar(d, _)) if not AUX_GT.isSubtypeByName(c, d, env, CT):
                    noSolution = True
                    break

                # 3
                case FGJ_GT.SubTypeC(FGJ.NonTypeVar(c, _), FGJ_GT.TypeVarA(b)):
                    # adding or constraints to c_prime
                    upperC = FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar("Object", FrozenList()))
                    # finfing upperbound constraint
                    for con in C_prime:
                        match con:
                            case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(d, _)) if a == b:
                                upperC = con
                                newC_prime.remove(con)
                                break
                    lowerupperBs.append((constraint, upperC, False))
                    newC_prime.remove(constraint)
                    new_constraint = FGJ_GT.SubTypeC(constraint.t1, upperC.t2)
                    newC_prime.add(new_constraint)
                    removeLater.add(new_constraint)

                # implied by a < C<>, a < b
                case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(c, _)):
                    found_second_constraint = False
                    for constraint2 in C_prime:
                        match constraint2:
                            case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a1), FGJ_GT.TypeVarA(b)) if a == a1:
                                b = AUX_GT.find_highest_b(b, C_prime)
                                found_second_constraint = True
                                break

                    if not found_second_constraint:
                        continue

                    upperC = FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar("Object", FrozenList()))
                    for con in C_prime:
                        match con:
                            case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b1), FGJ.NonTypeVar(_, _)) if b1 == b:
                                upperC = con
                                break

                    newlowerupperelem = (FGJ_GT.SubTypeC(constraint.t2, FGJ_GT.TypeVarA(b)), upperC, True)
                    if newlowerupperelem not in lowerupperBs:
                        lowerupperBs.append(newlowerupperelem)


            # 2 Arguments
            # 2
            # early break if no solution is possible in this constraint set (C_prime)
            if noSolution:
                break

            for constraint2 in C_prime:
                if constraint == constraint2:
                    continue

                match constraint, constraint2:
                    case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(c, _)), FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(d, _)) if a == b and not AUX_GT.isSubtypeByName(c, d, env, CT) and not AUX_GT.isSubtypeByName(d, c, env, CT):
                        noSolution = True
                        break

            # early break if no solution is possible in this constraint set (C_prime)
            if noSolution:
                break

        # skip to next C_prime because the current has no solution
        if noSolution:
            continue

        # check if expandLB additions are sound
        if removeLater:
            C_prime = reduceAndAdapt(newC_prime, env, CT)

            for constraint in C_prime:
                match constraint:
                    case FGJ_GT.SubTypeC(FGJ.NonTypeVar(c, _), FGJ.NonTypeVar(d, _)) if not AUX_GT.isSubtypeByName(c, d, env, CT):
                        noSolution = True
                        break

                for constraint2 in C_prime:
                    if constraint == constraint2:
                        continue

                    match constraint, constraint2:
                        case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(c, _)), FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(d, _)) if a == b and not AUX_GT.isSubtypeByName(c, d, env, CT) and not AUX_GT.isSubtypeByName(d, c, env, CT):
                            noSolution = True
                            break
        if noSolution:
            continue

        # to preserve an ordering
        oc_to_ord: dict[FGJ_GT.oc, list[list[FGJ_GT.sc]]] = dict()

        # solving expandLB
        for lowerC, upperC, addSub in lowerupperBs:
            cts = lowerC.t1
            dts = upperC.t2
            if type(cts) is not FGJ.NonTypeVar or type(dts) is not FGJ.NonTypeVar:
                raise Exception("CANT GO HERE - BUT TYPECHECKER")
            xs = FrozenList(FGJ.TypeVar("x" + str(i)) for i, _ in enumerate(cts.types))
            ns = AUX_GT.genericSupertypeList(cts.name, xs, dts.name, env, CT)
            # no order -> different solutions
            new_oc = frozenset(frozenset([FGJ_GT.EqualC(lowerC.t2, AUX.substitute_typeVars(cts.types, xs, ni))]) for ni in ns)
            if addSub:
                # new_oc = {{=}, {=}} |= {{<}} -> {{<}, {=}, {=}
                k = frozenset([frozenset([FGJ_GT.SubTypeC(lowerC.t2, lowerC.t1)])])
                new_oc |= k
            oc_to_ord[new_oc] = [[FGJ_GT.EqualC(lowerC.t2, AUX.substitute_typeVars(cts.types, xs, ni))] for ni in ns]
            if addSub:
                oc_to_ord[new_oc] = [[FGJ_GT.SubTypeC(lowerC.t2, lowerC.t1)]] + oc_to_ord[new_oc]
            C_prime |= {new_oc}

        C_prime = C_prime.difference(removeLater)

        # step 3
        for C_prime2 in AUX_GT.gen_C_prime(C_prime, oc_to_ord):
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
                            newTempC2 = AUX_GT.substConstraint(t, FGJ_GT.TypeVarA(a), temp_C2)
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
            if changed or not AUX_GT.is_solved_form(C_prime2):
                yield from Unify(C_prime2, env, CT)
                return

            if not AUX_GT.is_solved_form(C_prime2):
                raise Exception("NOT IN SOLVED FORM: " + C_prime2)

            # step 5
            changes = True
            while changes:
                changes = False

                newTempC2 = C_prime2.copy()
                for constraint in C_prime2:
                    match constraint:
                        case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b)):
                            newTempC2.remove(constraint)
                            newTempC2 = AUX_GT.substConstraint(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b), newTempC2)
                            newTempC2.add(FGJ_GT.EqualC(FGJ_GT.TypeVarA(b), FGJ_GT.TypeVarA(a)))
                            changes = True
                            break

                C_prime2 = newTempC2.copy()

            newTempC2 = C_prime2.copy()
            for constraint in C_prime2:
                match constraint:
                    case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b)) if a == b:
                        newTempC2.remove(constraint)

            C_prime2 = newTempC2.copy()

            C_prime2 = AUX_GT.NonTypeVarToTypeVar(C_prime2, env)

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
            Zs_fresh = [next(z_fresh) for _ in ass]

            o = {c.t1: AUX_GT.substitute_typeVarAs(Zs_fresh, ass, c.t2) for c in C_equal} | {c.t1: c.t2 for c in C_sub if type(c.t2) is FGJ.TypeVar} | {ai: zi for ai, zi in zip(ass, Zs_fresh)}

            assert len(Zs_fresh) == len(ass)

            y: dict[FGJ.TypeVar, FGJ.NonTypeVar] = {o[c.t1]: AUX_GT.substitute_typeVarAs(Zs_fresh, ass, c.t2) for c in C_sub if type(c.t2) is FGJ.NonTypeVar}

            yield o, y
