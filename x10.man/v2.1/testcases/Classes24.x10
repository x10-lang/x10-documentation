 package Classes.And.Type.Conversions.For.Sea.Urchins;
class Poly {
  public val coeff : ValRail[Int];
  public def this(coeff: ValRail[Int]) { this.coeff = coeff;}
  public static operator (a:Int) as Poly = new Poly([a]);
  public static def main(Rail[String]):Void {
     val three : Poly = 3 as Poly;
  }
}
