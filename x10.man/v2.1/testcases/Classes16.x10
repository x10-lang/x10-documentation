 package Classes.Are.For.Grasses.In.Mountain.Passes;
 class Crate(n:Int) {
  def this() { property(0); }
  // And to prove that the nullary constructor knows n==0:
  static def confirm() {
    val v : Crate{self.n == 0} = new Crate();
  }
 }