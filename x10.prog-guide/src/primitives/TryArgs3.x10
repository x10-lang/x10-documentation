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
 * TryArgs2 illustrates that a value like an Int that is passed as a var
 * argument may be modified in the method, but that modification does
 * not affect the caller.  What happens if you pass a reference, rather
 * than a value?  Here we pass a reference to an instance of TryArgs3.
 * In tryargs, the reference to c is reset, but in main(), c remains as
 * it was.
 */

public class TryArgs3 {
   public var value: Int;
   public def this(n: Int) { value = n; }
   
   public static def tryargs(var c: TryArgs3) {
      c = new  TryArgs3(1);
      Console.OUT.print("In tryargs, c is "+c.value);
   }
   public static def main(args: Array[String](1)): Void {
      var c: TryArgs3 = new TryArgs3(0);
      tryargs(c);
      Console.OUT.println(".  In main, c is "+c.value);     
   }
}

