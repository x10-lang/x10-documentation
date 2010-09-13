 package Clocks.For.Jocks.In.Clicky.Smocks;
class Example{
static def S():Void{}
static def alpha_phase_two():Void{}
static def beta_phase_two():Void{}
static def example() {
//alpha
val c = Clock.make();
c.resume();
async clocked(c) {
  // beta;
  c.next();
  beta_phase_two();
}
c.next();
alpha_phase_two();
} }