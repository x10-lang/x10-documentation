 package TypeDefs.glip.second;
 import x10.util.*;
 class LnSn {
 def example() {
type Nonnull[T] = T{self!=null};
type LnSn = Nonnull[List[Nonnull[String]]];
var example : LnSn;
}}