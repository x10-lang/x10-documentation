 package state.meant.labe.L;
 class Example {
 def example(a:(Int,Int) => Int, do_things_to:(Int)=>Int) {
lbl : for ([i] in 1..10) {
   for ([j] in i..10) {
      if (a(i,j) == 0) break lbl;
      if (a(i,j) == 1) continue lbl;
      do_things_to(a(i,j));
   }
}
} }