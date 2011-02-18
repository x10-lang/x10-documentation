
class Fib {
  val fib2:Int; // fib(n-2)
  val fib1:Int; // fib(n-1)
  val fib:Int;  // fib(n)
  def this(n:Int) {
    finish {
      async {
        val p = here.next();
        fib2 = at(p)
         n<=1 ? 0 : new Fib(n-2).fib;
      }
      fib1 = n<=0 ? 0 :
         n<=1 ? 1 : new Fib(n-1).fib;
    }
    fib = fib2+fib1;
  }
}
class CloneExample {
  def clone[T](o:T) { return at (here) o;  }
}

class LeakIt {
	static def foo(a:Any) {}
}
class Inheritance {
	class A {
	  val a:Int;
	  def this() {
		LeakIt.foo(this); //ERR
		this.a = 1;
		val me = this; //ERR
		LeakIt.foo(me);
		this.m2(); // so m2 is implicitly non-escaping
	  }
	  // permitted to escape
	  final def m1() {
		LeakIt.foo(this);
	  }
	  // implicitly non-escaping
	  final def m2() { // ERR Warning: Method 'm2()' is called during construction and therefore should be marked as @NonEscaping.
		LeakIt.foo(this); //ERR
	  }
	  // explicitly non-escaping
	  @NonEscaping final def m3() {
		LeakIt.foo(this); //ERR
	  }
	}
	class B extends A {
	  val b:Int;
	  def this() {
		super();
		this.b = 2;
		super.m3();
	  }
	}
}

class Dynamic {
	abstract class A {
	  val a1:Int;
	  val a2:Int;
	  def this() {
		this.a1 = m1(); //ERR
		this.a2 = m2();
	  }
	  abstract def m1():Int;
	  @NoThisAccess abstract def m2():Int;
	}
	class B extends A {
	  var b:Int = 3;
	  def this() {
		super();
	  }
	  def m1() {
		val x = super.a1;
		val y = this.b;
		return 1;
	  }
	  @NoThisAccess def m2() {
		val x = super.a1; //ERR
		val y = this.b; //ERR
		return 2;
	  }
	}
}
class Exception {
	class A{}
	class B extends A {
	  def this() {
		// Parsing error if super is not first! 
		//try { super(); } catch(e:Throwable){} //err
	  }
	}
}
class Outer {
  val a:Int;
  def this() {
    // Outer.this is raw
    Outer.this. new Inner(); //ERR
    new Nested(); // ok
    a = 3;
  }
  class Inner {
    def this() {
      // Inner.this is raw, but
      // Outer.this is cooked
      val x = Outer.this.a;
    }
  }
  static class Nested {}
}

class Constraints {
  val i0:Int; //ERR
  var i1:Int;
  var i2:Int{self!=0}; //ERR
  var i3:Int{self!=0} = 3;
  var i4:Int{self==42}; //ERR
  var s1:String;
  var s2:String{self!=null}; //ERR
  var b1:Boolean;
  var b2:Boolean{self==true}; //ERR
}

class Properties {
	class A(a:Int) {
	  def this(x:Int) {
		property(x);
	  }
	}
	class B(b:Int) {b==a} extends A {
	  val f1 = a+b;
	  val f2:Int;
	  val f3:A{this.a==self.a};
	  def this(x:Int) {
		super(x);
		val i1 = super.a;
		val i2 = this.b; //ERR
		val i3 = this.f1; //ERR
		f2 = 2; //ERR
		property(x);
		f3 = new A(this.a);
	  }
	}
}
