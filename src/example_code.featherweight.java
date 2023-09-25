class A<> extends Object<> {
    id(x) {
        return new A();
    }
}

class B<> extends A<> {
    id(x) {
        return new A();
    }
}

new Object()
