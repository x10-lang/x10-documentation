
class Position(x: Int, y: Int) {
   def this(x:Int,y:Int){property(x,y);}
   }
class Line(start: Position,
           end: Position{self != start}) {}
