 package Types.For.Gripes.About.Pipes;
  class A {} class B extends A{} class C extends A{}
 class D {
static def pick(t:Boolean, b:B, c:C) = t ? b : c;
}