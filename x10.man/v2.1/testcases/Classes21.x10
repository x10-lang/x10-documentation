 package Classes.In.Poly104o;
 class Poly {
   public val coeff : ValRail[Int];
   public def this(coeff: ValRail[Int]) { this.coeff = coeff;}
   public def degree() = coeff.length()-1;
   public def  a(i:Int) = (i<0 || i>this.degree()) ? 0 : coeff(i);

   public operator this + (p:Poly) =  new Poly(
      ValRail.make[Int](
         Math.max(this.coeff.length(), p.coeff.length()),
         (i:Int) => this.a(i) + p.a(i)
      ));
    public operator (n : Int) + this = new Poly([n]) + this;
   public operator this + (n : Int) = new Poly([n]) + this;

   def makeSureItWorks() {
      val x = new Poly([0,1]);
      val p <: Poly = x+x+x;
      val q <: Poly = 1+x;
      val r <: Poly = x+1;
   }

 }