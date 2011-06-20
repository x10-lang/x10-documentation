import x10.util.Ordered;
import x10.util.Random;
import x10.util.StringBuilder;
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
 * in-the-middle and shared-memory, single Place parallelism.
 * Small improvement possible by using as pivot the median of the
 * first, last, and middle element of the slice, rather than just
 * the middle always (R. Sedgwick).  For more history and pointers
 * to other refinements, 
 * <a  href="http://en.wikipedia.org/wiki/Quicksort">
 *    the Wikipedia article on quicksort
 * </a>
 * is a reasonable start.
 */
public class QSort {
   /**
    * top-level call: sorts the input array in ascending order
    * in place using the quicksort algorithm.
    * @param data the array of Ints to be sorted.
    */
   public static def sort[T](data: Array[T](1)){T <: Ordered[T]} {
      val r = data.region; // == the interval used to index data()
      finish sort[T](data, r.min(0), r.max(0));
   }
   private static val INSERTION_LIMIT  = 10;
   /*
    * Spawns threads only as needed to divide up the work
    * of sorting a slice of the data array from left to right.
    * @param data the whole Array to be sorted
    * @param left the first index in a subarray to be sorted by
    *    this call
    * @param right the last index in a subarray to be sorted by
    *    this call
    */
   private static def sort[T](data:Array[T](1), var left:Int, var right:Int){T <: Ordered[T]} {
      //Console.OUT.println("sort("+left+", "+right+")");
      while(true) {
         var i: Int = left;
         var j: Int = right;
         if (right - left <= INSERTION_LIMIT) {
            insertionSort(data, left, right);
            return;
         }
         val pivot = data(left + (right-left)/2);
 	      while (i <= j) {
	         while (data(i) < pivot) i++;
	         while (data(j) > pivot) j--;
	         if (i <= j) {
	            val tmp = data(i);
	            data(i++) = data(j);
	            data(j--) = tmp;
	         }
	      }
	      if (left < j) { 
	         if (i < right) {  // two slices to sort: use async for one
	            val iVal : Int = i, rightVal : Int = right;
	            async sort[T](data, iVal, rightVal);
	            right = j;     // sort from current left to j
	         }
	         else right = j;
	      }
	      else if (i < right) { // just sort from i to current right
	         left = i; 
	      }
	      else return;
      }
   }
   
   /* This procedure sorts in ascending order */
   private static def insertionSort[T](data: Array[T](1), left:Int, right:Int){T <: Ordered[T]} {
      //Console.OUT.println("Insert "+left+","+right);
      for(var i:Int = left+1; i<=right; i++) { 
         val value = data(i);  // next value to insert
   		var j:Int = i - 1;
   		while(true) {         // shift value's successors to the right
   			if (data(j) > value) {
   			   data(j + 1) = data(j);
   				j = j - 1;
   				if (j < left) break;
   			}
   			else break;
   		}
   		data(j + 1) = value;  // and then insert it
      }
   }
   /*
    * code from this point on is just here to allow you to exercise
    * the sort.
    */
   private static def showData[T](data:Array[T](1), leader: String, lineEnder:(Int)=>String) {
      Console.OUT.println(leader);
      val end = data.size - 1;
      if (end < 25) {
	      for (var i: Int = 0; i<end; i++) { 
	         Console.OUT.print(""+data(i)+lineEnder(i)); 
	      }
	   }
      else {
         val breakpoint = 28;
         for (var i: Int = 0; i<=breakpoint; i++) {
            Console.OUT.print(""+data(i)+lineEnder(i)); 
         }
         Console.OUT.println(""+data(breakpoint+1)+"...\r\n");
         val start = data.size - (breakpoint+2);
         for(var i: Int = start; i<end; i++) {    
            Console.OUT.print(""+data(i)+lineEnder(i-start)); 
         }
      }
      Console.OUT.println(""+data(data.size-1));
      Console.OUT.println("\r\n=====================\r\n");
   }
   
   private static def randomStrings(howMany: Int, maxLength: Int) {
      val X = new Random();
      val empty = MyString("");
      val data: Array[MyString](1) = new Array[MyString](howMany, empty);
      var totalLength: Int = 0;
      for(var n: Int = 0; n < howMany; ++n) {
         var length: Int = X.nextInt(128*1024);
         while(length <= 0) length = X.nextInt(128*1024);
         length = length%maxLength+1;
         totalLength += length;
	      val buffer = new StringBuilder();
	      for(var i:Int = 0; i<length; i++) {
	         var ascii: Int = X.nextInt(27);
	         while(ascii <= 0) ascii = X.nextInt(27);
	         buffer.add((64+ascii) as Char);
	      }
	      data(n) = MyString(buffer.toString());
      }
      Console.OUT.println("Average string length is "+(totalLength/howMany)+"\r\n");
      return data;
   }
   
   private static def verify[T](data: Array[T](1), howMany: Int){T <: Ordered[T]} {
      val last = data.size - 2;
      val X = new Random();
      val seen = new Array[Boolean](data.size, (Int) => false);
      for(var n: Int = 0; n<howMany; n++) {
         var index: Int = X.nextInt(last);
         while(seen(index)) index = X.nextInt(last);
         if (data(index) > data(index+1)) {
            Console.ERR.println("Sort failed at index "+index);
            Console.ERR.println("\t'"+data(index)+"'");
            Console.ERR.println("\t'"+data(index+1)+"'");
         }
      }
   }
   
   public static def main(args:Array[String](1)) {
      val N = args.size>0 ? Int.parse(args(0)) : 100; // data array size
      val V = args.size>1 ? Int.parse(args(1)) : 0;   // how many to check
      val S = args.size>2 ? args(2).equals("-s") : false; // strings or ints?
      if (S) {
         val M = args.size>3 ? Int.parse(args(3)) : 40;  // max string length
         val data = randomStrings(N, M);
         val lineEnder = (i: Int) => ((i&1)==1?"\r\n":", ");
         showData(data, "UNSORTED:\r\n", lineEnder);
         sort[MyString](data);
         if(V > 0) verify(data, V);
         showData(data, "SORTED:\r\n", lineEnder);
      }
      else {
         val X = new Random();
	      val randI = (Int) => MyInt(X.nextInt(999999)); 
	      val data: Array[MyInt](1) = new Array[MyInt](N, randI);
	      val lineEnder = (i: Int) => (i%10==9?"\r\n":", ");
	      showData(data, "UNSORTED:\r\n", lineEnder);
	      sort[MyInt](data);
	      if (V>0) verify(data, V);
	      showData(data, "SORTED\r\n", lineEnder);
      }
   }
   
   private static struct MyInt implements Ordered[MyInt] {
      public me: Int;
	   public def this(n: Int) { me = n;}
	   public def toString(): String = me.toString();
	   public operator this < (myInt: MyInt): Boolean { return (me < myInt.me); }
	   public operator this > (myInt: MyInt): Boolean { return (me > myInt.me); }
	   public operator this <= (myInt: MyInt): Boolean { return (me <= myInt.me); }
	   public operator this >= (myInt: MyInt): Boolean { return (me >= myInt.me); }
   }
   
   private static struct MyString implements Ordered[MyString] {
      public me: String;
	   public def this(s: String) { me = s;}
	   public def toString(): String = me;
	   public operator this < (myString: MyString): Boolean { return (me < myString.me); }
	   public operator this > (myString: MyString): Boolean { return (me > myString.me); }
	   public operator this <= (myString: MyString): Boolean { return (me <= myString.me); }
	   public operator this >= (myString: MyString): Boolean { return (me >= myString.me); }
   }
}
