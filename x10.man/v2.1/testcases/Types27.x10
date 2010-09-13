package triangleExample;
 class Position(x: Int, y: Int) {
    def this(x:Int,y:Int){property(x,y);}
    }
 class Line(start: Position,
            end: Position{self != start}) {}

class Triangle
 (a: Line,
  b: Line{a.end == b.start},
  c: Line{b.end == c.start && c.end == a.start})  {
   def this(a:Line,
            b: Line{a.end == b.start},
            c: Line{b.end == c.start && c.end == a.start})
   {property(a,b,c);}
 }
