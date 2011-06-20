public class VarIsVal {
   var anInt: Int = 231;
   public static def main(argc: Array[String]) {
      var vIsV: VarIsVal = new VarIsVal();
      Console.OUT.println("Start with: "+vIsV.anInt);
      vIsV.bumpMe();
      Console.OUT.println("End with: "+vIsV.anInt);
   }
   def bumpMe() {
      at(here.next()) {
         this.anInt++;
         Console.OUT.println("In bumpMe: "+this.anInt);
      }
   }
}