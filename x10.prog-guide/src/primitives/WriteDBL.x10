public class WriteDBL { 
   public static def main(args: Array[String](1)) {
//START TeX: writedbl
      val I  = new File(args(0));
      val W  = new FileWriter(I); // \xlref{writedbl-W}
      while(true) {// \xlref{writedbl-while}
        val line = Console.IN.readLine().trim();// \xlref{writedbl-trim}
        if (line.length() == 0) break; // \xlref{writedbl-break}
        val dbl = Double.parse(line); // \xlref{writedbl-dbl}
        W.writeDouble(dbl);// \xlref{writedbl-write}
      }
      W.close(); // \xlref{writedbl-close}
    } 
//END TeX: writedbl
}
