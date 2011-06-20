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
//START TeX: mpicluster
import x10.util.Random;
/**
 * A parallel version of the Monte Carlo estimate for pi that uses 
 * several Places and several threads at each place.
 */
public class MontePiCluster {
    /**
     * At the current Place, spawn some threads, each of which
     * generates n random points and return the total number
     * (combining all of the threads results) that fell inside
     * the circle.
     * @param pId: this process's id: used to create the seed for the
     *    random number generator.
     * @param threads: how many threads to use at this Place
     * @param n: how many points for each thread to generate
     * @return the total for all the threads of the number of points
     * that landed inside the circle. 
     */
//START TeX: countatp
    public static def countAtP(pId: Int, threads: Int, n: Long) {
        var count: Long = 0;
        finish for (j in 1..threads)  {
            val jj = j;
            async {
                val r = new Random(jj*Place.MAX_PLACES + pId);
                val rand = () => r.nextDouble();
                val jCount = countPoints(n, rand);
                atomic count += jCount;// \xlref{countatp-atomic}
            }
        }
        return count;
    }
    /**
//END TeX: countatp
     * Generate n points at random in the unit square, and return
     * the number that fell within the unit circle.
     * @param n the number of points to generate
     * @param rand the function generating the random numbers
     * @return the number of points that landed in the circle
     */
    public static def countPoints(n:Long, rand:()=>Double) {
        var inCircle: Long = 0;
        for (j in 1..n) {
            val x = rand();
            val y = rand();
            if (x*x +y*y <= 1.0) inCircle++;
        }
        return inCircle;
    }
   /**
    * There are three optional command line arguments: args(0) is the
    * number of points to generate, and args(1) is the number of
    * parallel activities to use, and args(2) is the number of 
    * threads to use at each Place.
    */
   public static def main(args: Array[String](1)) {
      val N = args.size > 0 ? Long.parse(args(0)) : 1000000L;
      val places = args.size > 1 ? Int.parse(args(1)) : Place.MAX_PLACES;
      val tPerP = args.size > 2 ? Int.parse(args(2)) : 4;
      val nPerT = N/(places * tPerP);
      val inCircle = new Array[Long](1..places);
      finish for(k in 1..places) {
         val kk = k;
         val pk = Place.place(k-1);
         async inCircle(kk) = at(pk) countAtP(kk, tPerP, nPerT);
      }
      var totalInCircle: Long = 0;
      for(k in 1..places) {
         totalInCircle += inCircle(k);
      }
      val pi = (4.0*totalInCircle)/(nPerT * tPerP * places);
      Console.OUT.println("Our estimate for pi is " + pi);
   }
}
//END TeX: mpicluster
