 package Classes.In.Poly106;
 class Poly {
   public val coeff : ValRail[Int];
   public def this(coeff: ValRail[Int]) { this.coeff = coeff;}
   public def degree() = coeff.length()-1;
   public def  a(i:Int) = (i<0 || i>this.degree()) ? 0 : coeff(i);
  public operator - this = new Poly(
    ValRail.make[Int](coeff.length(), (i:Int) => -coeff(i))
    );
   def makeSureItWorks() {
      val x = new Poly([0,1]);
      val p <: Poly = -x;
   }
 }