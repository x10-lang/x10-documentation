 package Classes.And.Implicit.Coercions;
 class Poly {
   public val coeff : ValRail[Int];
   public def this(coeff: ValRail[Int]) { this.coeff = coeff;}
   public def degree() = coeff.length()-1;
   public def  a(i:Int) = (i<0 || i>this.degree()) ? 0 : coeff(i);
   public final safe def toString() = {
      var allZeroSoFar : Boolean = true;
      var s : String ="";
      for( [i] in 0..this.degree() ) {
        val ai = this.a(i);
        if (ai == 0) continue;
        if (allZeroSoFar) {
           allZeroSoFar = false;
           s = term(ai, i);
        }
        else
           s +=
              (ai > 0 ? " + " : " - ")
             +term(ai, i);
      }
      if (allZeroSoFar) s = "0";
      return s;
   }
   private final safe def term(ai: Int, n:Int) = {
      val xpow = (n==0) ? "" : (n==1) ? "x" : "x^" + n ;
      return (ai == 1) ? xpow : "" + Math.abs(ai) + xpow;
   }

  public static safe operator (c : Int) : Poly = new Poly([c]);

  public static operator (p:Poly) + (q:Poly) = new Poly(
      ValRail.make[Int](
        Math.max(p.coeff.length(), q.coeff.length()),
        (i:Int) => p.a(i) + q.a(i)
     ));

  public static def main(Rail[String]):Void {
     val x = new Poly([0,1]);
     x10.io.Console.OUT.println("1+x=" + (1+x));
  }
}