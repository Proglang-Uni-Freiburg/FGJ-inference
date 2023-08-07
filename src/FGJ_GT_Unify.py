import FGJ_AST as FGJ
import FGJ_GT_AST as FGJ_GT
import FGJ_auxiliary_typing as AUX
import FGJ_GT_auxiliary_functions as AUX_GT


def Unify(C: FGJ_GT.C, env: FGJ.Delta, CT: FGJ.ClassTable) -> tuple[dict[FGJ.Type, FGJ.Type], FGJ.GenTypeAno]:
    #                        -//-                          -> tuple[dict[FGJ_GT.TypeVarA, FGJ.Type], FGJ.GenTypeAno]:
    for C_prime in AUX_GT.gen_C_prime(C):
        # step 1
        changed = True
        while changed:
            changed = False
            for constraint in C_prime:
                match constraint:
                    # 1 Argument

                    # adapt
                    case FGJ_GT.SubTypeC(FGJ.NonTypeVar(n1, ts), FGJ.NonTypeVar(n2, us)) if AUX_GT.isSubtypeByName(n1, n2, CT):
                        xs = [FGJ.TypeVar("x" + str(i)) for i, _ in enumerate(ts)]
                        ns = AUX_GT.genericSupertype(n1, xs, n2, CT)
                        C.remove(constraint)
                        subtedns = [AUX.sub(ts, xs, ni) for ni in ns]
                        C.add(FGJ_GT.EqualC(FGJ.NonTypeVar(n2, subtedns), FGJ.NonTypeVar(n2, us)))
                        changed = True

                    case FGJ_GT.SubTypeC(FGJ.TypeVar(n1), FGJ.NonTypeVar(n2, us)) if AUX_GT.isSubtypeByName(env[FGJ.TypeVar(n1)].name, n2, CT):
                        ns = AUX_GT.genericSupertype(env[FGJ.TypeVar(n1)].name, env[FGJ.TypeVar(n1)].types, n2, CT)
                        C.remove(constraint)
                        C.add(FGJ_GT.EqualC(FGJ.NonTypeVar(n2, ns), FGJ.NonTypeVar(n2, us)))
                        changed = True

                    # reduce
                    case FGJ_GT.EqualC(FGJ.NonTypeVar(c, ts), FGJ.NonTypeVar(d, us)) if c == d:
                        C.remove(constraint)
                        for ti, ui in zip(ts, us):
                            C.add(FGJ_GT.EqualC(ti, ui))
                        changed = True

                    # equals
                    case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b)):
                        equals: list[FGJ_GT.SubTypeC] = AUX_GT.findCircle(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b), C)
                        for sc in equals:
                            C.remove(sc)
                            C.add(FGJ_GT.EqualC(sc.t1, sc.t2))
                            changed = True

                    # erase
                    case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b)) if a == b:
                        C.remove(constraint)
                        changed = True

                    case FGJ_GT.EqualC(FGJ.TypeVar(x), FGJ.TypeVar(y)) if x == y:
                        C.remove(constraint)
                        changed = True

                    # swap
                    case FGJ_GT.EqualC(FGJ.NonTypeVar(n, ts), FGJ_GT.TypeVarA(a)):
                        C.remove(constraint)
                        C.add(FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(n, ts)))
                        changed = True

                    # 2 Arguments
                for constraint2 in C_prime:
                    if constraint == constraint2:
                        continue

                    match constraint, constraint2:

                        # match
                        case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(c, _)), FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(d, _)) if a == b:
                            if AUX_GT.isSubtypeByName(c, d, CT):
                                C.remove(constraint2)
                                C.add(FGJ_GT.SubTypeC(constraint.t2, constraint2.t2))
                                changed = True
                            elif AUX_GT.isSubtypeByName(d, c, CT):
                                C.remove(constraint)
                                C.add(FGJ_GT.SubTypeC(constraint2.t2, constraint.t2))
                                changed = True

                        # adopt
                        case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ.NonTypeVar(c, cs)), FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(d, _)) if AUX_GT.isConnected(FGJ_GT.TypeVarA(b), FGJ_GT.TypeVarA(a), C):
                            C.add(FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(c, cs)))
                            changed = True

        # step 2
        noSolution = False
        for constraint in C_prime:
            # skip step 2 if C_prime is already in solved form
            if AUX_GT.is_solved_form(C_prime):
                break

            match constraint:
                # 1 Argument
                # Own C<Ts> = D<Us> -> No solution
                case FGJ_GT.EqualC(FGJ.NonTypeVar(_), FGJ.NonTypeVar(_)):
                    noSolution = True
                    break

                # 1
                case FGJ_GT.SubTypeC(FGJ.NonTypeVar(c, _), FGJ.NonTypeVar(d, _)) if not AUX_GT.isSubtypeByName(c, d, CT):
                    noSolution = True
                    break

                # 3
                case FGJ_GT.SubTypeC(FGJ.NonTypeVar(c, ts), FGJ_GT.TypeVarA(b)):
                    # adding or constraints to c_prime
                    upperC = FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar("Object", []))
                    # finfing upperbound constraint
                    for con in C_prime:
                        match con:
                            case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(b), FGJ.NonTypeVar(d, us)):
                                upperC = con
                                C_prime.remove(con)
                                break
                    C_prime.remove(constraint)
                    C_prime.add(AUX_GT.expandLB(constraint, upperC, CT))

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

        # skip to next C_prime because the current has no solution
        if noSolution:
            continue

        # step 3
        for C_prime2 in AUX_GT.gen_C_prime(C_prime):
            changed = False
            noSolution = False

            for constraint in C_prime2:
                match constraint:
                    case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), t):
                        if AUX_GT.occoursIn(FGJ_GT.TypeVarA(a), t):
                            noSolution = True
                            break
                        AUX_GT.subConstraint(t, FGJ_GT.TypeVarA(a), C_prime2)
                        # (a = T) but T/a?
                        # C.remove(FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), t))
                        # C.add(FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), t))
                        changed = True

            # skip this C_prime2 because it has no solution
            if noSolution:
                continue

            # step 4
            if changed:
                # can we just return here? Should be fine
                return Unify(C_prime2, env, CT)

            # step 5
            # not sure if we can do both rules in one for-loop since sub may produce a case fpr elim
            for constraint in C_prime2:
                match constraint:
                    # is this exhaustively
                    case FGJ_GT.SubTypeC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b)):
                        C.remove(constraint)
                        AUX_GT.subConstraint(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b), C_prime2)
                        C_prime2.add(FGJ_GT.EqualC(FGJ_GT.TypeVarA(b), FGJ_GT.TypeVarA(a)))

            for constraint in C_prime2:
                match constraint:
                    case FGJ_GT.EqualC(FGJ_GT.TypeVarA(a), FGJ_GT.TypeVarA(b)) if a == b:
                        C_prime2.remove(constraint)

            # step 6
            C_equal: set[FGJ_GT.EqualC] = set()
            C_sub: set[FGJ_GT.SubTypeC] = set()

            for constraint in C_prime2:
                match constraint:
                    case FGJ_GT.EqualC(_):
                        C_equal.add(constraint)
                    case FGJ_GT.SubTypeC(_):
                        C_sub.add(constraint)

            ass: list[FGJ_GT.TypeVarA] = [c.t1 for c in C_equal]
            Ys_fresh = [FGJ.TypeVar("Y" + str(i)) for i, _ in enumerate(ass)]
            # why only X in C_sub? why not all T?
            o = {c.t1: AUX_GT.sub(Ys_fresh, ass, c.t2) for c in C_equal} | {ai: yi for ai, yi in zip(ass, Ys_fresh)} | {c.t1: c.t2 for c in C_sub}
            # what is yi? all c from C_sub?
            y = ... # {yi: sub(Ys_fresh, ass, c.t2) for c in C_sub}
            return o, y
