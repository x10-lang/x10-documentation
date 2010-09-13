 package exp.re.ssio.ns.fiel.dacc.ess;
class Uncle {
  public static val f = 1;
}
class Parent {
  public val f = 2;
}
class Ego extends Parent {
  public val f = 3;
  class Child extends Ego {
     public val f = 4;
     def expDotId() = this.f; // 4
     def superDotId() = super.f; // 3
     def classNameDotId() = Uncle.f; // 1;
     def cnDotSuperDotId() = Ego.super.f; // 2
  }
}
