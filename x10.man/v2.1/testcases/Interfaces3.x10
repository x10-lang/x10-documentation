 package Interface.Field.Two;
 interface KnowsPi {PI = 3.14159265358;}
class Circle implements KnowsPi {
  static def area(r:Double) = PI * r * r;
}
