package Overview.Mat2;
abstract class Mat(rows:Int, cols:Int) {
 static type Mat(r:Int, c:Int) = Mat{self.rows==r&&self.cols==c};
 static def makeMat(r:Int,c:Int) : Mat(r,c) = null;
 abstract operator this + (y:Mat(this.rows,this.cols))
                 :Mat(this.rows, this.cols);
 abstract operator this * (y:Mat) {this.cols == y.rows}
                 :Mat(this.rows, y.cols);
  static def example(a:Int, b:Int, c:Int) {
    val axb1 : Mat(a,b) = makeMat(a,b);
    val axb2 : Mat(a,b) = makeMat(a,b);
    val bxc  : Mat(b,c) = makeMat(b,c);
    val axc  : Mat(a,c) = (axb1 +axb2) * bxc;
  }
}