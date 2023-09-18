class Int<> extends Object<> {
    mult(num) {
        return num;
    }
}


class Pair<X extends Object<>, Y extends Object<>> extends Object<> {
    X fst;
    Y snd;
}

class MultPair<> extends Object<> {
    m(p) {
        return p.fst.mult(p.snd);
    }

    mm(p, q) {
        return new Pair(p.fst, q.snd);
    }

    mmm(p) {
        return p.mult(p);
    }
}

new Object()
