 @det
 def histogram(N:Int, A:Rail[Int(0..N)]):Rail[Int](N+1) {
    val result = new Rail[Acc[Int]](N+1, (Int)=>new Acc[Int](0,Int.+));
    finish for (i in A.values()) async {
       result(i) <- 1;
    }
    return new Rail[Int](N+1, (i:Int)=> result(i));
 }