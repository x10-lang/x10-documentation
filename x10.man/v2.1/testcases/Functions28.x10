 package expsome.Functions28;
class Span(low:Int, high:Int) {def this(low:Int, high:Int) {property(low,high);} def between(n:Int) = low <= n && n <= high;}
public class Functions28{
  def check(digit:Span!) throws Exception = digit.between.(Int);  }