 package exp.ress.io.ns.numeric.conversions;
 class ExampleOfConversionAndStuff {
 def example() {
val f : (Int)=>Boolean = (Int) => true;
val n : Byte = 123 as Byte; // explicit
val ok = f(n); // implicit
 } }