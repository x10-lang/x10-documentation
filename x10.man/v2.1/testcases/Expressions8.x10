 package expressions.stupid.addab;
 class Example {
 def example(A:()=>Rail[Int], I: () => Int, B: () => Int ) {
{
  val aa = A();  // Evaluate A() once
  val ii = I();  // Evaluate I() once
  val bb = B();  // Evaluate B() once
  val tmp = aa(ii) + bb; // read aa(ii)
  aa(ii) = tmp;  // write sum back to aa(ii)
}
}}