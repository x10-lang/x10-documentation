public class ReadDBL { // see the file files/ReadDBL.x10
//START TeX: readdbl
   public static def main(args: Array[String](1)) {
      val inputPath  = args(0);
      val I  = new File(inputPath);
      val R  = new FileReader(I);
      while(true) {// \xlref{readdbl-while}
        Console.OUT.println(R.readDouble());
      }// \xlref{readdbl-ehilw}
    } 
//END TeX: readdbl
}

