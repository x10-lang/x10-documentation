/*
 *  This file is part of the X10 project (http://x10-lang.org).
 *
 *  This file is licensed to You under the Eclipse Public License (EPL);
 *  You may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *      http://www.opensource.org/licenses/eclipse-1.0.php
 *
 *  (C) Copyright IBM Corporation 2006-2010.
 */
import x10.util.Random;
import x10.io.Console;
/**
 * This is a modestly improved version of MontePi1.x10, refactored to
 * make it easier to parallelize.  See MontePi1.x10 for more comments
 * on the substance of what is being done.
 */
public class MontePi2 {
   /**
    * Estimates pi by choosing n points at random in the unit 
    * square.
    * @param n the number of points to compute
    * @param rand the function to call for the next random number
    *     between 0 and 1 inclusive
    * @return the approximation to pi as a Double.
    */
   //START TeX: mpi2cp
   public static def countPoints(n: Int, rand: ()=>Double) {
      var inCircle: Int = 0;
      for (j in 1..n) {
         val x = rand();
         val y = rand();
         if (x*x +y*y <= 1.0) inCircle++;
      }
      return inCircle;
   }
   //END TeX: mpi2cp
   
   /**
    * The optional first entry in args is the number of points
    * to generate.  The default is 10,000.
    */
//START TeX: mpi2-N
   public static def main(args: Array[String](1)) {
       val N = args.size > 0 ? Int.parse(args(0)) : 10000;
       //START TeX: mpi2main
//END TeX: mpi2-N
       val r = new Random();              //\xlref{mpi2main-r}
       val rand = () => r.nextDouble();   //\xlref{mpi2main-rand}
       val inCircle = countPoints(N, rand); //\xlref{mpi2main-incircle}
       val pi = (4.0 * inCircle)/N;       //\xlref{mpi2main-pi}
       //END TeX: mpi2main
       Console.OUT.println("Our estimate for pi is " + pi);
   }
}
