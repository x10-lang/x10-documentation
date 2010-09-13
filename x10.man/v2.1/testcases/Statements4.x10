 package Sta.tem.ent.s.expressions;
 import x10.util.*;
class StmtEx {
  def this() { x10.io.Console.OUT.println("New StmtEx made");  }
  static def call() { x10.io.Console.OUT.println("call!");  }
  def example() {
     var a : Int = 0;
     a = 1; // assignment
     new StmtEx(); // allocation
     call(); // call
  }
}
