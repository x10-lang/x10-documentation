 package expsome.Functions29;
class Span(low:Int, high:Int) {def this(low:Int, high:Int) {property(low,high);} def between(n:Int) = low <= n && n <= high;}
public class Functions29{
  def check(digit:Span!) throws Exception = (n:Int) => digit.between(n);  }