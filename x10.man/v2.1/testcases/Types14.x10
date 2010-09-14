 package ch4;
class Set[-T] {
  var x: T;
  def this(x: T) { this.x = x; }
  def set(x: T) = { this.x = x; }
  def summary(): String = this.x.typeName();
  static def example() {
    val s : Set[Object] = new Set[Object](new Throwable());
    s.summary(); // == "x10.lang.Throwable"
    s.set("A String");
    s.summary(); // == "x10.lang.String";
  }
}
