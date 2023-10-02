class A<X extends Object<>> extends Object<> {
	X a;
	seta(x) {
		return new A(x);
	}
}

class B<X extends Object<>, Y extends Object<>> extends A<X> {
	Y b;
	setb(x) {
		return new B(this.a, x);
	}
	setboth(x, y) {
		return new B(x, y);
	}
	swap() {
		return new B(this.b, this.a);
	}
}

new Object()
