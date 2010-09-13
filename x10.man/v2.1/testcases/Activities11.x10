 package Activities.And.Protein;
 class CASSizer{
var target:Object = null;
public atomic def CAS(old1: Object, new1: Object): Boolean {
   if (target.equals(old1)) {
     target = new1;
     return true;
   }
   return false;
}
}