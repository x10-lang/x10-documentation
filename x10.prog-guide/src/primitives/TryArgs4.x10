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
/**
 * Illustrates that when you pass a reference as a val argument, you
 * can assign values to the fields of the object referenced, and
 * those modifications are visible in the caller, which here is
 * main().
 */
public class TryArgs4 {
   public var value: Int;
   public def this(n: Int) {
   	value = n;
   }
   
   public static def tryargs(c: TryArgs4) {
      c.value = 1;
      Console.OUT.print("In tryargs, c is "+c.value);
   }
   
   public static def main(args: Array[String](1)): Void {
      var c: TryArgs4 = new TryArgs4(0);
      tryargs(c);
      Console.OUT.println(".  In main, c is "+c.value);     
   }
}