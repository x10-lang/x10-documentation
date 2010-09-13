 package statements.FOR.block.heads;
 class Example {
 def example(b:Boolean, S1:(Int)=>Void, S2:(Int)=>Void ) {
if (b) {
  // This is a block
  val v = 1;
  S1(v);
  S2(v);
}
  } }