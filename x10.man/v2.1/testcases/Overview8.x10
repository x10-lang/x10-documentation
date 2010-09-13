package Overview.ObjectAndPlaces;
 class FHolder{
 var f : Int = 0;
 static def example(x:FHolder) {
val xhere = x as FHolder!;
xhere.f = 12;
}}