 package Functions2.Span;
class Span(low:Int, high:Int) {
  def this(low:Int, high:Int) {property(low,high);}
  def between(n:Int) = low <= n && n <= high;
  def example() {
    val digit = new Span(0,9);
    val isDigit : (Int) => Boolean = digit.between.(Int);
    if (isDigit(8)) x10.io.Console.OUT.println("8 is!");
  }
}
