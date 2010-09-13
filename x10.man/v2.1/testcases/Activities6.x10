 package Activities.Activities.Activities;
 class EquivCode {
 static def S(p:Place) {}
 static def example(D:Dist) {
foreach (p in D.places()) at (p) {
    foreach (pt in D|here) {
        S(p);
    }
}
}}