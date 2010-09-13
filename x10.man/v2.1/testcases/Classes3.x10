 package classes.fields.primus;
class Super{
  val f = 1;
}
class Sub extends Super {
  val f = true;
  def superf() : Int = super.f; // 1
}
