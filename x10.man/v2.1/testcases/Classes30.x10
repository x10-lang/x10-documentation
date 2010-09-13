package Classes.Are.For.Wussies.Wimps.And.People.With.Vowels.In.Their.Names;
class MyRegion(rank:Int) {
  static type MyRegion(n:Int)=MyRegion{self.rank==n};
  def this(r:Int):MyRegion(r) {
    property(r);
  }
  def this(diag:ValRail[Int]):MyRegion(diag.length){
    property(diag.length);
  }
  def mockUnion(r:MyRegion(rank)):MyRegion(rank) = this;
  def example() {
    val R1 : MyRegion(3) = new MyRegion([4,4,4]);
    val R2 : MyRegion(3) = new MyRegion([5,4,1]);
    val R3 = R1.mockUnion(R2); // inferred type MyRegion(3)
  }
}
