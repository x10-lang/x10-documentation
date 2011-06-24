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
import x10.util.concurrent.AtomicLong;

/**
 * This is a parallel version of MontePi2.x10.  It uses multiple 
 * threads on a single processor.  See MontePi.x10 for more comments
 * on the substance of what is being done.
 */
public class MontePiAsync2 {
    /**
    * Finds n random points in the unit square and returns the
    * number that actually lie in the unit circle.
    * @param n the number of points to compute
    * @param rand the function to call for the next random number
    *     between 0 and 1 inclusive
    * @return the number (out of n tries) that landed in the circle.
    */
    public static def countPoints(n: Long, rand: ()=>Double) {
        var inCircle: Long = 0;
        for (j in 1..n) {
            val x = rand();
            val y = rand();
            if (x*x +y*y <= 1.0) inCircle++;
        }
        return inCircle;
    }

    /**
     * There are two optional command line arguments: args(0) is the
     * number of points to generate, and args(1) is the number of
     * parallel activities to use.  The latter is bounded by runtime's
     * limit on the number of activities for a single processor.
     */
    public static def main(args: Array[String](1)) {
        val N = args.size > 0 ? Long.parse(args(0)) : 100000L;
        val threads = args.size > 1 ? Int.parse(args(1)) :  4;

        val nPerThread = N/threads;
        val inCircle = new AtomicLong(0);

        finish for(k in 1..threads) {
            val r = new Random(k*k + k + 1);   
            val rand = () => r.nextDouble();
//START TeX: montepiasync2Addandget
            async inCircle.addAndGet(countPoints(nPerThread, rand));
//END TeX: montepiasync2Addandget
        }
        val pi = 4.0 * inCircle.get()/(nPerThread*threads);
        Console.OUT.println("Our estimate for pi is " + pi);
    }
}
