 package classes.guards.invariants.glurp2;
 class Pt(x:Int, y:Int){}
class Line(a:Pt, b:Pt{a != b}) {}
