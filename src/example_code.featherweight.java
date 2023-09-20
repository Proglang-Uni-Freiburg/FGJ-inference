class Int<> extends Object<> {
    id(x) {
        return x;
    }
}

class SomeMethods<> extends Object<> {
    idd(x) {
        return x.id(x);
    }
}

class Pair<X extends Int<>, Y extends Int<>> extends SomeMethods<> {
    X fst;
    Y snd;

    setfst(newfst) {
        return new Pair(newfst, this.snd);
    }

    setboth(newfst, newsnd) {
        return new Pair(this.setfst(newfst).fst, this.idd(newsnd.id(newsnd)));
    }
}

new Object()

