 package statements.come.from.banks.and.cranks;
 class LabelledBreakeyBreakyHeart {
 def findy(a:ValRail[ValRail[Int]], v:Int): Boolean {
var found: Boolean = false;
outer: for (var i: Int = 0; i < a.length; i++)
    for (var j: Int = 0; j < a(i).length; j++)
        if (a(i)(j) == v) {
            found = true;
            break outer;
        }
 return found;
}}