 package Classes.Are.For.Grasses;
class Crate(n:Int) {
  def this() : Crate{self.n==0} = { property(0); }
  def this(b:Boolean) : Crate{self.n==1} = { property(1); }
}
