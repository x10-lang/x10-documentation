 package Clocks.Finish.Hates.Clocks;
 class Example{
 def example() {
val c:Clock = Clock.make();
async clocked(c) {                // (A)
      finish async clocked(c) {   // (B) Violates clause 2
            next;                 // (Bnext)
      }
      next;                       // (Anext)
}
 } }