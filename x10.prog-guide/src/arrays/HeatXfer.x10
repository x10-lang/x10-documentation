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
//import x10.util.Random;
import x10.util.Random;

/**
 * We give here a simple example using Arrays built on general Regions.
 * The averaging we do here is a technique that comes up in the numerical
 * solution of certain kinds of partial differential equations.  We point
 * this out only to assure you that we didn't just make this example up 
 * in order to have something to show you.
 * 
 * The story starts with a Region B whose Points consist of 2 flavors:
 * boundary Points and interior Points.  Your intuition should be that a
 * Point is a boundary Point (is "on the boundary") if there are nearby
 * points not also in the Region.  
 * 
 * The plot thickens. At the beginning of the computation, we have an
 * Array[Double] T whose Region is B.  Think of it as assigning a
 * temperature to each Point in the Region.  Given a temperature Array,
 * we can transform it to a new one by averaging as follows:
 *       If b is a boundary Point, its temperature remains fixed
 *       If p is an interior Point, its temperature becomes the average
 *          of its current temperature with the temperatures of its
 *          nearest neighbors that are also in B.
 * Two Points p and q are nearest neighbors when
 *          They agree in all but one of their coordinates
 *          If the coordinate at which they disagree is the k-th,
 *             then p(k)-q(k) is either 1 or -1
 * Eg the nearest neighbors of (0,0) are (-1,0), (1,0), (0,-1) and (0,1),
 * but not (1,1) and so on.  A Point of rank r has 2*r nearest neighbors.
 * They are exactly the integer points in the ball of radius 1 about the
 * Point.
 * 
 * If we repeat this averaging process, the temperature distribution will
 * soon stabilize ("reach equilibrium").  This gives us a (rather
 * idealized) model of the temperature distribution of a body whose
 * surface temperature is maintained at some constant distribution (by
 * outside forces) coming to equilibrium in its interior.  Again, the
 * physics, however interesting, is not the point, which is just to show
 * how to use Array's API effectively.
 * 
 * We are going to use a concrete subclass BlobWithBdry of x10.lang.Region
 * to represent our Region.  BlobWithBdry.x10 can be found in this
 * directory.  It allows us to represent Regions with boundaries that
 * are essentially arbitrary--at the cost of being expensive to iterate
 * through.  To keep our example easy to understand we are going to 
 * work here with the very simple case of hemispherical bowl: the
 * points (x,y,z) that satisfy
 *                   x*x  + y*y + z*z <= r*r
 * constitute the ball of radius r centered at (0,0,0), and our bowl
 * consists of all points in that ball with z <= 0, the bottom
 * hemisphere.
 * 
 * We're going to decree that the boundary consists of those Points
 * whose distance from the origin is some (small) amount bw less than
 * the radius r.
 */ 

public class HeatXfer {
   private val B: BlobWithBdry{rank == 3}; // the region's X10 representation
   private val T: Array[Double](B.rank);   // "temperature" array
   private static NEIGHBORS <: Array[Point(3)] = 
      [                 // neighbors of (0,0,0)
         Point.make(-1, 0, 0), Point.make(1, 0 ,0) as Point(3),
         Point.make( 0,-1, 0), Point.make(0, 1, 0),
         Point.make( 0, 0,-1), Point.make(0, 0, 1)
      ];
   
   /**
    * construct the hemispherical bowl with outer radius r and 
    * inner radius r-bw as described in the class's comment.
    * @param r the outer radius of the bowl
    * @param bw the boundary width: points in bowl AND in the ball
    * of radius r-bw are in the interior.
    */
   public def this(r: Int, bw: Int) {
      val box: Region{rank==3, rect} = (-r..r) * (-r..r) * (-r..0);
      val inBowl = (p:Point) => inTheBowl(p, r*r, (r-bw)*(r-bw));
      val B = new BlobWithBdry(box, inBowl);
      val rand = new Random();
      val assignTemp = (p:Point) =>
               B.contains(p) ? rand.nextDouble() : Double.NaN;
      this.B = B;
      this.T = new Array(B, assignTemp);
   }
   
   /**
    * Assume the usual x-y-z coordinates: x,y plane is the horizontal plane,
    * and z is the vertical coordinate, so that being restricted to z < 0,
    * our bowl opens "up".
    * @param p a rank-3 Point that may or may not be in the bowl
    * @param outer the square of the radius of the containing ball
    * @param inner the square of the radius of the inner ball
    * @return 1 if p is in the interior, 0 if p is in the boundary layer,
    * and -1 otherwise.
    */
   private static def inTheBowl(p: Point, outerSq: Int, innerSq: Int): Int {
      if (p(2) > 0) return -1; // p is above the bowl
      var lengthSq: Int = p(0)*p(0) + p(1)*p(1) + p(2)*p(2);   
      return lengthSq <= innerSq ?  1 :
             lengthSq <= outerSq ?  0 :
             -1;
   }
   
   /**
    * For each point p in the interior of the bowl, we average the 
    * temperatures at that point together with its 6 nearest neighbors.
    * Not all the neighbors may be in the bowl, though, so we are
    * careful to count only those that are.  The upshot is to update
    * T(p) to the average.
    */
   public def average() {
      for(p in T) {
         if(B.isInTheInterior(p)) {
            var count: Int    = 1;
            var sum:   Double = T(p);
            for(n in NEIGHBORS.values()) {
               val translated = p + n;
               if (B.contains(translated)) {
                  sum  += T(translated);
                  count += 1;
               }
            }
            T(p) = sum/count; 
         }
      }
   }
      
   private static RANGE_OUTPUT = "The %s ranges are\r\n   all:  (%f, %f)\r\n%s";
   /**
    * Displays the max and min values of the temperature over the
    * whole bowl, the interior and the boundary
    * @param time a short description of the point in the process
    *    when this is being called.
    */
   public def display(time: String) {
      val max = T.reduce((a: Double, b: Double)=>Math.max(a, b), Double.MIN_VALUE);
      val min = T.reduce((a: Double, b: Double)=>Math.min(a, b),  Double.MAX_VALUE);
      Console.OUT.println(String.format(RANGE_OUTPUT, [time, min, max, displayParts()]));
   }
   private static PARTS_OUTPUT = "   bdy:  (%f, %f)\r\n   int:  (%f, %f)";
   /**
    * used by display() to get the interior and boundary figures.
    */
   public def displayParts() {
      var bmin: Double =  Double.MAX_VALUE, bmax: Double = Double.MIN_VALUE, 
          imin: Double =  Double.MAX_VALUE, imax: Double = Double.MIN_VALUE;
      for(p in B as Region) {
         val tAtP = T(p);
         if (B.isOnTheBoundary(p)) {
            if (tAtP < bmin) bmin = tAtP;
            else if (tAtP > bmax) bmax = tAtP;
         } else {
            if (tAtP < imin) imin = tAtP;
            else if (tAtP > imax) imax = tAtP;
         }
      }
      return String.format(PARTS_OUTPUT, [bmin as Any, bmax, imin, imax]);
   }
   
   public static def main( args: Array[String](1) ) {
      var r:  Int = -1,  // radius
          bw: Int = -1,  // boundary width
          iterations: Int = 5; // how often to average
       for(var i:Int = 0; i<args.size; i += 2) {
         val value = Int.parse(args(i+1));
         val key = args(i)(1); 
         if (key == 'b')      bw = value;
         else if (key == 'i') iterations = value;
         else if (key == 'r') r = value;
         else {
            Console.ERR.println("HeatXfer: parameters are -b, -r, -d" 
                    + " -t and -i, not \""+args(i)+"\"");
            at(Place.FIRST_PLACE) System.setExitCode(5);
            return;
         }
      }
      if (r == -1) r = 50;
      if (bw == -1) bw = Math.ceil(0.01*r) as Int;
      
      val data =  new HeatXfer(r, bw);  // creates the Region and initializes
      Console.OUT.println("Radius r = "+r+", boundary width "+bw+
      		              " and "+iterations+" iterations.");
      Console.OUT.print("There are "+data.B.size()+" points, with ");
      Console.OUT.print(""+data.B.boundarySize()+" in the boundary, and ");
      Console.OUT.println(""+data.B.interiorSize()+" in the interior.");
      data.display("opening");
      for(i in 1..iterations) data.average();
      data.display("final");
   }
}
