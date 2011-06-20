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
//START TeX: mpi1
import x10.util.Random; //\xlref{mpi1-imp}
//PAUSE TeX: mpi1
import x10.io.Console;

/**
 * A simple Monte-Carlo method is used to estimate the value of pi 
 * 
 * This program selects random points from the unit square in the
 * first quadrant of the 2D plane, [(0,0),(1,1)], or in other words
 * all (x,y) such that 0 <=x <= 1 and 0 <= y <= 1.  A point (x,y)
 * lies in the unit circle when it satisfies x*x + y*y <= 1.0.
 * So the probability that a random point (x,y) in the unit square
 * actually lies in the unit circle is pi/4.  So, if we choose
 * points at random, the fraction that land in the unit circle ought
 * to be close to pi/4 == .78..., which a little greater than 3/4,
 * but less than 4/5.  This gives us a way to estimate the value of
 * pi by using a random number generator.
 * 
 * This version is sequential.  Parallel to follow!
 */
//RESUME TeX: mpi1
public class MontePi1 {
    static val N = 10000; //\xlref{mpi1-N}
    public static def main(s: Array[String](1)) { // \xlref{mpi1-s}
        val r = new Random();   //\xlref{mpi1-r}
        var inCircle:Double = 0.0; //\xlref{mpi1-incircle}
        for (j in 1..N) { //\xlref{mpi1-for}
            val x = r.nextDouble(); //\xlref{mpi1-x}
            val y=  r.nextDouble(); //\xlref{mpi1-y}
            if (x*x +y*y <= 1.0) inCircle++; //\xlref{mpi1-if}
        }  //\xlref{mpi1-endfor},
        val pi = 4*(inCircle/N); //\xlref{mpi1-pi}
        Console.OUT.println("Our estimate for pi is " + pi); //\xlref{mpi1-out}
    }
}
//END TeX: mpi1
