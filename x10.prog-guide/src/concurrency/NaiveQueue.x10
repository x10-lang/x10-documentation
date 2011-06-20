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

import x10.util.concurrent.*;
/**
 * Naive, thread-safe implementation of a queue.
 * 
 * This implementation uses a huge array rather than a circular buffer,
 * trading storage for simplicity.  Attempts to write outside the
 * buffer cause a null return, and to read an empty buffer cause
 * the return of a value prescribed in the constructor.  The aim
 * here, to repeat, is simplicity at the cost of storage.
 * 
 * Items arrive at the queue's end and are removed from its start.
 * 
 */
public class NaiveQueue[T] {
   private var first:Int = 0;
   private var next: Int = 0;
   public  val buffer: Array[T](1);
   private val initialValue: T;

   /** 
    * constructor using the default zero (normally "null") as the initial
    * value for the buffer entries.  The type T of array elements must
    * satisfy the "haszero" constraint.  Such types have a well-defined
    * default zero value, which can be computed using Zero.get[T](0).
    * All classes satisfy this constraint (null being the default zero),
    * as do all of the numeric types, for which 0 is (surprise!) the
    * default zero.
    * @param size how many entries in the buffer
    */
   public def this(size: Int){T haszero} {
      this(size, Zero.get[T]());
   }
   /** 
    * constructor using a given value as the initial value for the buffer
    * entries;
    * @param size how many entries in the buffer
    * @param initialValue the initialValue to use
    */
   public def this(size: Int, initialValue: T) {
      this.buffer = new Array[T](size, initialValue);
      this.initialValue = initialValue;
   }   
   /**
    * Returns the current number of elements in the queue, an ephemeral
    * value if ever there were one.
    * @return the current number of elements in the queue
    */
   public def size() = next-first; 
   /**
    * append an item to the end of the queue
    * @param t the item to append
    * @return this queue (apparently the accepted convention), null if
    * the buffer is full.
    */
   public def addLast(t: T): NaiveQueue[T] {
      atomic {
         if (next < buffer.size) {
            buffer(next++) = t;
            return this;
         }
         else {
            Console.ERR.println("Queue overflow: "+this.size()+" entries remain");
            return null;
         }
      }
   }
   /**
    * remove the first element in the list and return it.
    * @return the element removed if there is one, the value used to 
    * initialize the buffer otherwise.
    */
   public def removeFirst(): T {
      atomic {
         if (next > first) {
            return buffer(first++);
         }
         else {
            Console.ERR.println("Attempt to remove item from an empty queue");
            return initialValue;
         }
      }
   }
}
