 package Arrays.Some.Examples.Fidget.Fidget;
 class Example {
 static def example() {
val MAX_HEIGHT=20;
val Null = Region.makeUnit();  // Empty 0-dimensional region
val R1 = 1..100; // 1-dim region with extent 1..100
val R2 = [1..100] as Region(1); // same as R1
val R3 = (0..99) * (-1..MAX_HEIGHT);
val R4  = [0..99, -1..MAX_HEIGHT] as Region(2); // same as R3
val R5 = Region.makeUpperTriangular(10);
val R6 = R4 && R5; // intersection of two regions
 } }