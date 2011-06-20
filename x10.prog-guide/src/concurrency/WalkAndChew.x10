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
 * Simple
 */
public class WalkAndChew {
   public static def bigComputation(first: Int, second: Int) {
      var a: String = "a";
      var b: String = "b";
      var answer: String = "";
      for(var m: Int = 0; m < first; m++) {
         answer += a;
         for(var n: Int =0; n< second; n++) {
            answer += b;
         }
      }
      return answer;
   }
   public static def main(args: Array[String](1)) {
      //START TeX: walkandchew
      val n = 3;
      val big1: GlobalRef[Cell[String]] = GlobalRef[Cell[String]](new Cell[String]("!"));
      val big2: GlobalRef[Cell[String]] = GlobalRef[Cell[String]](new Cell[String]("2"));
      val pMain = here;   // \xlref{walkandchew-pMain}
      finish { // \xlref{walkandchew-finish}
         async at(Place.place(0)) { // \xlref{walkandchew-async1}
            val bc1 = bigComputation(n,n);
            at(big1.home) big1()() = bc1; // \xlref{walkandchew-big1}
         }
         async at(Place.place(0)) { // \xlref{walkandchew-async2}
            val bc2 = bigComputation(n,n);
            at(big2.home) big2()() = bc2; // \xlref{walkandchew-big2}
         }
      } // \xlref{walkandchew-finishend}
      //PAUSE Tex: walkandchew
      Console.OUT.println("big1()=" + big1() + " and that()=" + big1()());
      Console.OUT.println("big2()=" + big2() + " and that()=" + big2()());
      //RESUME TeX: walkandchew
      assert big1()().equals(big2()()); // \xlref{walkandchew-assert}
      //END TeX: walkandchew
   }
}
