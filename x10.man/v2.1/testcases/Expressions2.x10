 package exp.vexp.pexp.lexp.shexp;
class Outer {
  val inner : Inner = new Inner();
  class Inner {
    val outer : Outer = Outer.this;
  }
  def alwaysTrue() = (this == inner.outer);
}
