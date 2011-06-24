class DblDbl_Struct {
static
//START TeX: dbldblStruct
public  struct DblDbl {// \xlref{dbldblStruct-struct}
   public val x: Double;// \xlref{dbldblStruct-x}
   public val y: Double;// \xlref{dbldblStruct-y}
   public def this(a: Double, b: Double) { // \xlref{dbldblStruct-def}
      this.x = a; this.y = b;
   }
   public def normSq() = x*x + y*y;
}
//END TeX: dbldblStruct
  public static def main(argv:Array[String](1)) {
//START TeX: dbldblstructCtorCall
     var p: DblDbl = DblDbl(1.2, 3.4);
//END TeX: dbldblstructCtorCall
  }
}

