 package classes.not.weasels;
 class Waif(rect:Boolean, onePlace:Place, zeroBased:Boolean) {
   def this(rect:Boolean, onePlace:Place, zeroBased:Boolean)
          :Waif{self.rect==rect, self.onePlace==onePlace, self.zeroBased==zeroBased}
          = {property(rect, onePlace, zeroBased);}
   property rail: Boolean = rect && onePlace == here && zeroBased;
   static def zoink() {
      val w : Waif{
w.rail
 }= new Waif(true, here, true);
 }}