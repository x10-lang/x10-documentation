/*
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
 * A thread-safe implementation of a queue using a modest circular buffer
 * (instead of a giant linear one as in NaiveQueueue.x10 or CleverQueue.x10).  
 */
public class CircularQueue[T]{T haszero} {
	/** the maximum queue length we'll allow */
	public val maximumSize: Int;
	/** if read mod maximumSize, the index of the first entry, if any */
	private var first: Int = 0;
	/** if read mod maximumSize, the index of the next slot to store into */
	private var  next:  Int = 0;
	/** bounded buffer to hold entries */
	public val buffer: Array[T](1);

	/**
	 * create a queue with the argument as its maximum size and the
	 * default zero for T used to populate the buffer.
	 * @param sizeLimit a bound on the number of entries permitted
	 */
	public def this(sizeLimit: Int) { this(sizeLimit, Zero.get[T]()); }
	/**
	 * create a queue with the argument as its maximum size and the
	 * buffer populated with the initial value.
	 * @param sizeLimit a bound on the number of entries permitted
	 */
	public def this(sizeLimit: Int, initialValue: T) { 
	   this.maximumSize = sizeLimit;
	   this.buffer = new Array[T](sizeLimit, initialValue);
	}
   /**
    * Addition of an element at the end of the queue.
    * @param t the item to be added
    * @return this
    */
	public def addLast(t: T): CircularQueue[T] {
	   when(next - first < maximumSize) {
	      this.buffer(next++ % this.maximumSize) = t;
	   }
	   return this;
	}
   /**
    * removes and returns the element at the beginning of the queue
	 * @return the element removed
    */
	public def removeFirst(): T {
	   when(first < next) {
	      return this.buffer(first++ % this.maximumSize);
	   }
	}
	/** returns the number of elements in the queue */
	public def getSize(): Int { atomic { return next -first; }}
}
