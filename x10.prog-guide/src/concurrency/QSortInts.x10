import x10.util.Ordered;
import x10.util.Random;
/*
 *  This file is part of the X10 project (http://x10-lang.org).
 *
 *  This file is licensed to you under the Eclipse Public License (EPL);
 *  You may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *      http://www.opensource.org/licenses/eclipse-1.0.php
 *
 *  (C) Copyright IBM Corporation 2006-2010.
 */

/**
 * Straightforward quicksort implementation using a naive partition-
 * in-the-middle and not bothering with well-known optimizations,
 * such as using insertion sort once the partitions get small.
 * This is only intended as a simple example of an array-based
 * program that combines a recursive divide and conquer algorithm 
 * with async and finish, not as a highly efficient sorting 
 * procedure.
 */
//START TeX: qsortints
public class QSortInts {   
   /**
    * top-level call: sorts the input array in place using the
    * quicksort algorithm.
    * @param data the array of Ints to be sorted.
    */
   public static def sort(data: Array[Int](1)) {
      val r = data.region;
      val first = r.min(0), last = r.max(0);
      sort(data, first, last); // \xlref{qsortints-sort}
   }
//PAUSE TeX: qsortints
   /**
    * Uses a pair of threads to divide the work of each recursive
    * call to this method.
    * @param data the whole Array to be sorted
    * @param left the first index in a subarray to be sorted by
    *    this call
    * @param right the last index in a subarray to be sorted by
    *    this call
    */
//RESUME TeX: qsortints
   public static def sort(data:Array[Int](1), 
             left:Int, right:Int) {
      var i: Int = left, j: Int = right;
      val pivot = data(left + (right-left)/2);// \xlref{qsortints-pivot}
      while (i <= j) {// \xlref{qsortints-while}
         while (data(i) < pivot) i++;
         while (data(j) > pivot) j--;
         if (i <= j) {
            val tmp = data(i);
            data(i++) = data(j);
            data(j--) = tmp;
         }
      }// \xlref{qsortints-endwhile}
      finish { // when you are here i > j // \xlref{qsortints-finish}
         if (left < j) async sort(data, left, j);
         if (i < right) async sort(data, i, right);
      }// \xlref{qsortints-endfinish}
   }
//END TeX: qsortints
   /*
    * code from this point on is just here to allow you to exercise
    * the sort.
    */
   private static def showData(data:Array[Int](1), leader: String) {
      Console.OUT.println(leader);
      val end = data.size - 1;
      if (end < 120) {
         for (var i: Int = 0; i<end; i++) { 
            Console.OUT.print(""+data(i)+(i%10==9?"\r\n":", ")); 
         }
      }
      else {
         val breakpoint = 58;
         for (var i: Int = 0; i<=58; i++) {
            Console.OUT.print(""+data(i)+(i%10==9?"\r\n":", ")); 
         }
         Console.OUT.println(""+data(59)+"...");
         val start = data.size - 60;
         for(var i: Int = start; i<end; i++) {    
            Console.OUT.print(""+data(i)+((i-start)%10==9?"\r\n":", ")); 
         }
      }
      Console.OUT.println(""+data(data.size-1));
      Console.OUT.println("\r\n=====================\r\n");
   }
   
   public static def main(args:Array[String](1)) {
      val N = args.size>0 ? Int.parse(args(0)) : 100;
      val R = new Random();
      val rand = (Int) => R.nextInt(4*N); // used to init "data"
      val data: Array[Int](1) = new Array[Int](N, rand);
      showData(data, "UNSORTED:\r\n");
      sort(data);
      showData(data, "SORTED:\r\n");
   }
}
