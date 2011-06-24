import x10.io.File;

public class FileIO {
//START TeX: fileio
   public static def main(args: Array[String](1)) {
      val inputPath  = args(0);
      val outputPath = args(1);
      val I = new File(inputPath); // \xlref{fileio-I}
      val O = new File(outputPath); // \xlref{fileio-O}
      val P = O.printer(); // \xlref{fileio-P}
      for (line in I.lines()) {// \xlref{fileio-for}
         P.print(line);
      }// \xlref{fileio-rof}
      P.flush();// \xlref{fileio-flush}
   }
//END TeX: fileio
}

