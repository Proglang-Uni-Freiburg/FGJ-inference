# FGJ-inference
Type inference for FGJ



Subtyping FGJ

In adapt Regel:

|- C< X* > <: D< N* >

Implementiert durch Funktion mit Eingabe C, X*, D und Ausgabe N*
Dabei ist X* Liste von frischen Typparametern.


∆ ⊢ T <: T (S-REFL)
∆ ⊢ S <: T ∆ ⊢ T <: U ∆ ⊢ S <: U (S-TRANS)
∆ ⊢ X <: ∆(X) (S-VAR)
class C <Y*◁ P*> ◁ C’{. . .} ∆ ⊢ C <: [T*/X*]N


genericSupertype( C, T*, D ) =
    C = D: return T*      (wegen S-REFL:     c< T* > <: c< T* >)
    C != D:  Regel (S-CLASS)
    class C< Y* ◁ P*  > ◁ C’< M* > {. . .}     -- in M* tauchen nur die Y*
    ---- [[[ Return C’ < [T* / Y*]M* > ]]]
    Return genericSupertype ( C’ , [T* / Y*]M* , D )


X=X -> rauswerfen zu reduce-regel dazu - fehlt im Paper
C<T*> = D<U*> -> unsolvable - fehlt im Paper

statt sets listen? sollte keinen unterschied machen (dublikate verhindern -> auch löschen oder ...)

füge bei equals auch an=a1 hinzu, sollte keinen unterschied machen

NEW QUESTIONS

step 2 rule 3 ?

step 3 remove add (T = a) why dont remove it

--

subConstraint does not use it's first parameter

---

duale rule for match and adopt - keep bigger one

match:
C<T> < a, D<V> < a          |- C<X> <: D<N>
------------------
C<T> < D<V>, D<V> < a

adopt:
C<T> < a, a <* b, D<U> < b
--------------------------
-//- + C<T> < b

match dont need delta

expandLB - check if subtype possible
 - add constraint C<T><D<U> and mark

----

Unify return o, ysEps

what is ysEps - all possible ys with their bound?
