 package Activities.For.Tactivities.At.Some.Home;
 class Example {
 def example(a:DistArray[Int](1), i:Int) {
async at (a.dist(i)) {
  a(i) += 1;
}
} }