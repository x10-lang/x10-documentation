 package Classes.In.Poly101;
 // Integer-coefficient polynomials of one variable.
 class Poly {
   public val coeff : ValRail[Int];
   public def this(coeff: ValRail[Int]) { this.coeff = coeff;}
   public def degree() = coeff.length()-1;
   public  def  a(i:Int) = (i<0 || i>this.degree()) ? 0 : coeff(i);

   public static safe operator (c : Int) as Poly = new Poly([c]);

   public safe def apply(x:Int) {
     val d = this.degree();
     var s : Int = this.a(d);
     for( [i] in 1 .. this.degree() ) {
        s = x * s + a(d-i);
     }
     return s;
   }

   public operator this + (p:Poly) =  new Poly(
      ValRail.make[Int](
         Math.max(this.coeff.length(), p.coeff.length()),
         (i:Int) => this.a(i) + p.a(i)
      ));
   public operator this - (p:Poly) = this + (-1)*p;

   public operator this * (p:Poly) = new Poly(
      ValRail.make[Int](
        this.degree() + p.degree() + 1,
        (k:Int) => sumDeg(k, this, p)
        )
      );


   public operator (n : Int) + this = (n as Poly) + this;
   public operator this + (n : Int) = (n as Poly) + this;

   public operator (n : Int) - this = (n as Poly) + (-1) * this;
   public operator this - (n : Int) = ((-n) as Poly) + this;

   public operator (n : Int) * this = new Poly(
      ValRail.make[Int](
        this.degree()+1,
        (k:Int) => n * this.a(k)
      ));
   private static def sumDeg(k:Int, a:Poly, b:Poly) {
      var s : Int = 0;
      for( [i] in 0 .. k ) s += a.a(i) * b.a(k-i);
        // x10.io.Console.OUT.println("sumdeg(" + k + "," + a + "," + b + ")=" + s);
      return s;
      };
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

   public static def Main(ss:Rail[String]) = main(ss);

  public static def main(Rail[String]):Void {
     val X = new Poly([0,1]);
     val t <: Poly = 7 * X + 6 * X * X * X;
     val u <: Poly = 3 + 5*X - 7*X*X;
     val v <: Poly = t * u - 1;
     for( [i] in -3 .. 3) {
       x10.io.Console.OUT.println(
         "" + i + "	X:" + X(i) + "	t:" + t(i)
         + "	u:" + u(i) + "	v:" + v(i)
         );
     }
  }

}