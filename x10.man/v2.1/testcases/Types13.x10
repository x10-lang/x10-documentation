 package ch4;
class Get[+T] {
  val x: T;
  def this(x: T) { this.x = x; }
  def get(): T = x;
  static def example() {
     val g : Get[Int]! = new Get[Int](31);
     val n : Int = g.get();
     x10.io.Console.OUT.print("It's " + n);
     x10.io.Console.OUT.print("It's still " + g.get());
  }
}