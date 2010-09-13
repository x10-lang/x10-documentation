 package Types.cripes.whered.you.get.those.gripes;
 class Matrix(rows:Int, cols:Int){
 public static def someMatrix(): Matrix = null;
 public static def example(){
  val a : Matrix = someMatrix() ;
  var b : Matrix{b.rows == a.cols} ;
}}