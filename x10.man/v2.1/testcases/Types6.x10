package not.x10.lang;
class Coords(x: Int, y: Int) {
  def this(x: Int, y: Int) : Coords{self.x==x, self.y==y}
    = { property(x, y); }
  def move(dx: Int, dy: Int) = new Coords(x+dx, y+dy);
}