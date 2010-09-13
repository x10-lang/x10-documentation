 package Structs.For.Muckts;
struct Polar(r:Double, theta:Double){
  def this(r:Double, theta:Double) {property(r,theta);}
  static val Origin = Polar(0,0);
  static val x0y1 = Polar(1, 3.14159/2);
}
