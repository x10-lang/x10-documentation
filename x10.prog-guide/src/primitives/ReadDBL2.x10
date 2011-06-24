public class ReadDBL2 {
//START TeX: readdbl2
   public static def main(args: Array[String](1)) {
      val inputPath  = args(0);
      val I  = new File(inputPath);
      var r: FileReader = null; // \xlref{readdbl2-r}
      try {// \xlref{readdbl2-try}
         r = new FileReader(I);// \xlref{readdbl2-setr}
         while(true) { // \xlref{readdbl2-while}
            Console.OUT.println(r.readDouble());
         }// \xlref{readdbl2-elihw}
      } catch(eof: x10.io.EOFException) { // \xlref{readdbl2-catch1}
            Console.OUT.println("Done!"); // \xlref{readdbl2-printdone}
      } catch(ioe: x10.io.IOException) {// \xlref{readdbl2-catch2}
        Console.ERR.println(ioe);// \xlref{readdbl2-printioe}
      } finally {// \xlref{readdbl2-finally}
        if (r != null) r.close(); // \xlref{readdbl2-user}
     }
   } 
//END TeX: readdbl2
}

