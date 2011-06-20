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
 * A less naive, thread-safe implementation of a queue.
 * 
 * This implementation still uses a huge array rather than a circular buffer,
 * trading storage for simplicity.  Attempts to read or write outside the
 * buffer simple cause a bounds exception to be thrown.  The aim here, to
 * repeat, is simplicity at the cost of storage.
 * 
 * Items arrive at the queue's end and are removed from its start.
 */
public class CleverQueue[T] {
   private val first = new AtomicInteger(0);
   private val next = new AtomicInteger(0);
   private val initialValue: T;
   public  val buffer: Array[T](1);

   /** 
    * constructor using the default zero (normally "null") as the initial
    * value for the buffer entries;
    * @param size how many entries in the buffer
    */
   public def this(size: Int){T haszero} { this(size, Zero.get[T]()); }

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
   public def size() { atomic { return next.get()-first.get(); }}
   /**
    * append an item to the end of the queue
    * @param t the item to append
    * @return this queue (apparently the accepted convention)
    */
   public def addLast(t: T): CleverQueue[T] {
      buffer(next.getAndAdd(1)) = t;
      return this;
   }
   /**
    * remove the first element in the list and return it.  This method
    * blocks when the queue is empty or the element it is looking for
    * has not yet been supplied.
    * @return the element removed
    */
   public def removeFirst(): T {
      val firstNow = first.getAndAdd(1); // reserve our slot
      when(buffer(firstNow) != initialValue) {
         return buffer(firstNow);
      }
   }
}