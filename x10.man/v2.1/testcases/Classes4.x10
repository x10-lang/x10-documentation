 package classes.fields.secundus;
class A {
   val f = 3;
}
class B extends A {
   val f = 4;
   class C extends B {
      val f = 5;
      def foo()
         = f          // 5
         + super.f    // 4
         + B.this.f   // 4 (the "f" of the outer instance)
         + B.super.f; // 3 (the "super.f" of the outer instance)
    }
}
