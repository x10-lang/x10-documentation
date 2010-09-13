package Classes.In.Poly101;
 // Integer-coefficient polynomials of one variable.
 class UglyPoly {
   public val coeff : ValRail[Int];
   public def this(coeff: ValRail[Int]) { this.coeff = coeff;}
   public def degree() = coeff.length()-1;
   public  def  a(i:Int) = (i<0 || i>this.degree()) ? 0 : coeff(i);

   public static safe operator (c : Int) as UglyPoly = new UglyPoly([c]);

   public safe def apply(x:Int) {
     val d = this.degree();
     var s : Int = this.a(d);
     for( [i] in 1 .. this.degree() ) {
        s = x * s + a(d-i);
     }
     return s;
   }

   public operator this + (p:UglyPoly) =  new UglyPoly(
      ValRail.make[Int](
         Math.max(this.coeff.length(), p.coeff.length()),
         (i:Int) => this.a(i) + p.a(i)
      ));
   public operator this - (p:UglyPoly) = this + (-1)*p;

   public operator this * (p:UglyPoly) = new UglyPoly(
      ValRail.make[Int](
        this.degree() + p.degree() + 1,
        (k:Int) => sumDeg(k, this, p)
        )
      );


   public operator (n : Int) + this = (n as UglyPoly) + this;
   public operator this + (n : Int) = (n as UglyPoly) + this;

   public operator (n : Int) - this = (n as UglyPoly) + (-1) * this;
   public operator this - (n : Int) = ((-n) as UglyPoly) + this;

   public operator (n : Int) * this = new UglyPoly(
      ValRail.make[Int](
        this.degree()+1,
        (k:Int) => n * this.a(k)
      ));
   private static def sumDeg(k:Int, a:UglyPoly, b:UglyPoly) {
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

   def mult(p:UglyPoly) = this * p;
   def mult(n:Int) = n * this;
   def plus(p:UglyPoly) = this + p;
   def plus(n:Int) = n + this;
   def minus(p:UglyPoly) = this - p;
   def minus(n:Int) = this - n;
   static def const(n:Int) = n as UglyPoly;

   public static def Main(x:Rail[String]) = main(x);
   public static def main(Rail[String]):Void {
      val X = new UglyPoly([0,1]);
      val t <: UglyPoly = 7 * X + 6 * X * X * X;

      val u <: UglyPoly = 3 + 5*X - 7*X*X;
      val v <: UglyPoly = t * u - 1;
      for( [i] in -3 .. 3) {
        x10.io.Console.OUT.println(
          "" + i + "	X:" + X(i) + "	t:" + t(i) + "	u:" + u(i) + "	v:" + v(i)
          );
      }
      uglymain();
   }

  public static def uglymain() {
     val X = new UglyPoly([0,1]);
     val t <: UglyPoly = X.mult(7).plus(X.mult(X).mult(X).mult(6));
     val u <: UglyPoly = const(3).plus(X.mult(5)).minus(X.mult(X).mult(7));
     val v <: UglyPoly = t.mult(u).minus(1);
     for( [i] in -3 .. 3) {
       x10.io.Console.OUT.println(
         "" + i + "	X:" + X.apply(i) + "	t:" + t.apply(i)
          + "	u:" + u.apply(i) + "	v:" + v.apply(i)
         );
     }
  }
}