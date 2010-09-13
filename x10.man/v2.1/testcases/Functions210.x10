 package Functions2.For.The.Lose;
 class TypecheckThatSillyExample {
   def checker() {
    val l1 : (String, String) => String = String.+;
    val r1 : (String, String) => String = (x: String, y: String): String => x + y;
    val l2 : (Long,Long) => Long = Long.-;
    val r2 : (Long,Long) => Long = (x: Long, y: Long): Long => x - y;
//var v1 : (Float,Float) => Float = Float.-(Float,Float) ;
var v2 : (Float,Float) => Float = (x: Float, y: Float): Float => x - y;
//var v3 : (Int) => Int =  Int.-(Int)     ;      ;
var v4  : (Int) => Int  =  (x: Int): Int => -x;
var v5 : (Boolean,Boolean) => Boolean = Boolean.&            ;
var v6 : (Boolean,Boolean) => Boolean =  (x: Boolean, y: Boolean): Boolean => x & y;
//var v7 : (Boolean) => Boolean = Boolean.!            ;
var v8 : (Boolean) => Boolean =  (x: Boolean): Boolean => !x;
//var v9 : (Int,Int) => Boolean = Int.<(Int,Int)       ;
var v10: (Int,Int) => Boolean =  (x: Int, y: Int): Boolean => x < y;
//var v11 : (Dist,Place)=>Dist = Dist.|(Place)        ;
var v12 : (Dist,Place)=>Dist=  (d: Dist, p: Place): Dist => d | p;
}
 }
