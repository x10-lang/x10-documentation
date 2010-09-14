 package Types.Inferred.By.Phone;
class Spot(x:Int) {
  def this() {property(0);}
  def this(xx: Int) { property(xx); }
}
class Confirm{
 static val s0 : Spot{x==0} = new Spot();
 static val s1 : Spot{x==1} = new Spot(1);
}