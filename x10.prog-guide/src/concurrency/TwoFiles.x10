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
import x10.io.File;

public class TwoFiles {
   /**
    * File objects are "passive": they just name objects in the file system
    * that may or may not exist.  The calls to I.lines() and J.lines() attempt
    * to open streams to read the files.  Since neither file exists, two
    * exceptions are thrown that cause these activities to abort.  X10's 
    * process scheduler will bundle the exceptions in an instance of
    * x10.lang.MultipleExceptions.  When the scheduler restarts the main
	 * activity, it throws the MultipleExceptions instance, and the "catch"
    * gets control.  It prints the bad news to the standard error stream.
    * The loop there shows how to get your hands on the individual exceptions
    * that occurred in the asyncs.
    */
   public static def main(args: Array[String](1)) {
      try {   
         finish {
            async {
               val I  = new File("not_here.txt");
               for (line in I.lines()) {
                  Console.OUT.print(line);
               }
            }
            async { 
               val J = new File("not_here_either.txt");
	            for(line in J.lines()) {
	               Console.OUT.print(line);
	            }
            }
         }
      } catch(e: MultipleExceptions) {
      	for (t:Throwable in e.exceptions.values()) {
      	   t.printStackTrace();
      	}
      }
   } 
 }