package Arrays.arrays.ginungagap.bakery.treats.doomed;
class Example{
def example() {
val A = new Array[Int](1..10, (p:Point(1))=>p(0) );
// A = 1,2,3,4,5,6,7,8,9,10
val cube = (i:Int) => i*i;
val B = new Array[Int](A.region); // B = 0,0,0,0,0,0,0,0,0,0
A.map(B, cube);
// B = 1,8,27,64,216,343,512,729,1000
} }