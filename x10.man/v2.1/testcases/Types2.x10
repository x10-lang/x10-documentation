 package Types.By.Cripes.Classes;
class Position {
  private var x : Int = 0;
  public def move(dx:Int) { x += dx; }
  public def pos() : Int = x;
}
