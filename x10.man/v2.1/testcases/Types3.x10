 package Types.For.Gripes.Of.Wesley.Snipes;
class Cell[T] {
  var empty : Boolean = true;
  var contents : T;
  public def putIn(t:T) {
    contents = t; empty = false;
  }
  public def emptyOut() { empty = true; }
  public def isEmpty() = empty;
  public def getOut():T throws Exception {
     if (empty) throw new Exception("Empty!");
     return contents ;
  }
}
