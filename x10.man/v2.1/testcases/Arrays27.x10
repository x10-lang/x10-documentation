package Arrays.Dists.Examples.Examples.EXAMPLESDAMMIT;
 class Example{
 def example() {
val R  <: Region = 1..100;
val D1 <: Dist = Dist.makeBlock(R);
val D2 <: Dist = R -> here;
 } }