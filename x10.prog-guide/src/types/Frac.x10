//START TeX: fracdef
class Frac implements Arithmetic[Frac], 
                      Arithmetic[Double] 
{
//END TeX: fracdef
  /*
  This is an example class for an introduction to interfaces.
  If we were doing it for real, we would make a number of changes.
  For example, we'd 
    -- use operators rather than methods, 
    -- provide coercions, 
    -- have Arithmetic take two arguments   
  */
  private val n:Int;
  private val d:Int;
  public def toString() = n + "/" + d; 
//START TeX: fracctor
  public def this(var n:Int, var d:Int) {
    if (d < 0) { n = -n; d = -d; }
    if (d == 0) throw new Exception("Division by zero!");
    var gcd : Int = gcd(n,d);
    this.n = n / gcd;
    this.d = d / gcd;
  }
//END TeX: fracctor

  // Fraction arithmetic.
//START TeX: fraconfrac
  public def add(f:Frac) = new Frac(n * f.d + f.n * d, d * f.d);
  public def negate() = new Frac(-n, d);
  public def subtract(f:Frac) = this.add(f.negate());
  public def multiply(f:Frac) = new Frac(n * f.n, d * f.d);
  public def divide(f:Frac) = new Frac(n * f.d, d * f.n);  
  
//END TeX: fraconfrac
  // Fraction and Double -> Double
  
//START TeX: fracondouble
  public def asDouble():Double = (n as Double) /(d as Double);
  public def add(dbl: Double) = this.asDouble() + dbl;
  public def subtract(dbl: Double) = this.asDouble() - dbl;
  public def multiply(dbl: Double) = this.asDouble() * dbl;
  public def divide(  dbl: Double) = this.asDouble() / dbl;
//END TeX: fracondouble
  
  public static def gcd(a:Int, b:Int):Int {
    // Euclid's Algorithm
    if (a == 0) return b;
    if (b == 0) return a;
    if (a == b) return a;
    if (a < 0) return -gcd(-a, b);
    if (b < 0) return -gcd(a,-b);
    val c = Math.max(a,b);
    val d = Math.min(a,b);
    val e = c % d;
    return gcd(d,e);
  }
  
  private static def gcdemo(a:Int, b:Int){
    Console.OUT.println("a="+a+"; b=" + b + "; gcd=" + gcd(a,b) );
  }
    
  public static def doIt(x:Arithmetic[Frac])  {
    
  }

  public static def main(argv:Array[String](1)) {
    val half = new Frac(10, 20);
    Console.OUT.println("half=" + half);
    val third = new Frac(7, 21);
    Console.OUT.println("third=" + third);
    val sixth = half.subtract(third);
    Console.OUT.println("sixth=" + sixth);
    val fivesixths = half.add(third);
    val one = fivesixths.add(sixth);
    Console.OUT.println("one=" + one);
    val one2 = half.divide(half);
    Console.OUT.println("one2=" + one2);
    val sixth2 = half.multiply(third);
    Console.OUT.println("sixth2=" + sixth2);
    
    // And with doubles...
    val x = .25;
    val y = half.multiply(x);
    Console.OUT.println("y ought to be about 0.125 and is " + y);
    
    // And the doIt method from the book
//START TeX: fracdoit
    doIt(new Frac(1,3));
//END TeX: fracdoit
  }  
  
}
