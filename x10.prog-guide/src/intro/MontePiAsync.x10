/*
 *  This file is part of the X10 project (http://x10-lang.org).
 *
 *  This file is licensed to You under the Eclipse Public License (EPL);
 *  You may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *     http://www.opensource.org/licenses/eclipse-1.0.php
 *
 *  (C) Copyright IBM Corporation 2006-2010.
 */
import x10.util.Random;

/**
 * This is a parallel version of MontePi2.x10.  It uses multiple 
 * threads on a single processor.  See MontePi.x10 for more comments
 * on the substance of what is being done.
 */
public class MontePiAsync {
   /**
    * Finds n random points in the unit square and returns the
    * number that actually lie in the unit circle.
    * @param n the number of points to compute
    * @param rand the function to call for the next random number
    *    between 0 and 1 inclusive
    * @return the number (out of n tries) that landed in the circle.
    */
   //START TeX: mpiacp
   public static def countPoints(n: Long, rand: ()=>Double) {
     var inCircle: Long = 0;
     for (j in 1..n) {
       val x = rand();
       val y = rand();
       if (x*x +y*y <= 1.0) inCircle++;
     }
     return inCircle;
   }
   //END TeX: mpiacp
   /**
   * There are two optional command line arguments: args(0) is the
   * number of points to generate, and args(1) is the number of
   * parallel activities to use.  The latter is bounded by runtime's
   * limit on the number of activities for a single processor.
   */
   public static def main(args: Array[String](1)) {
      //START TeX: mpia
      val N = args.size > 0 ? Long.parse(args(0)) : 100000L;  //\xlref{mpia-N}
      val threads : Int = args.size > 1 ? Int.parse(args(1)) :  4; //\xlref{mpia-threads}

      val nPerThread = N/threads; //\xlref{mpia-nperthread}
      val inCircle = new Array[Long](1..threads);   //\xlref{mpia-incircle}
 
      finish for(k in 1..threads) { //\xlref{mpia-for}
         val r = new Random(k*k + k + 1);       //\xlref{mpia-r}
         val rand = () => r.nextDouble();       //\xlref{mpia-rand}
         val kval = k;                     //\xlref{mpia-kval}
         async inCircle(kval) = countPoints(nPerThread, rand); //\xlref{mpia-async}
      }                                 //\xlref{mpia-endfor}

      var totalInCircle: Long = 0;             //\xlref{mpia-total}
      for(k in 1..threads) {      //\xlref{mpia-for2}
         totalInCircle += inCircle(k);         //\xlref{mpia-total2}
         Console.OUT.println("ic("+k+") = "+inCircle(k)); //\xlref{mpia-out}
      }                                 //\xlref{mpia-endfor2}

      val pi = (4.0*totalInCircle)/(nPerThread*threads); //\xlref{mpia-pi}
      //END TeX: mpia
      Console.OUT.println("Our estimate for pi is " + pi);
   }
}
