 package objects.dwiffle.and.a.half.a.moon;
 class C { }
 class D {
    var f:C=null;
 }
 class Fudders {
  def truly(b:Boolean) {}
 def plongent(P:Place, Q:Place) throws Exception {

val x = new C();
// C object o1 created, local reference stored in x.
at (P) {
      // In the body x contains a remote reference to o1
      val d = new D();
      d.f  = x; // remote reference stored in d.f
      truly(d.f == x);
      truly(x == x);
      at (Q) {
         // x continues to be a remote reference to o1.
         at (P) {
             truly(d.f == x);
             truly(x == x);
         }
      }
}
}}