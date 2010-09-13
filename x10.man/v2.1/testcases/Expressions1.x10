 package expsome.Expressions1;

public class Expressions1{
  def check(f:() => ((Int,Int)=>Int), a:()=>Int, b:()=>Int) throws Exception = f()(a(),b());  }