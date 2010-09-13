package Clocks.For.Jocks;
class Qlocked{
static def S():Void{}
static def flock() {
 val c1 = Clock.make(), c2 = Clock.make(), c3 = Clock.make();
  async clocked (c1, c2, c3) S
();
}}