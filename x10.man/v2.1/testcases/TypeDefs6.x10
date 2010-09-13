 import x10.util.*;
 class TypeDefBrow {
 def someTypeDefs () {
type StringSet = Set[String];
type MapToList[K,V] = Map[K,List[V]];
type Int(x: Int) = Int{self==x};
type Dist(r: Int) = Dist{self.rank==r};
type Dist(r: Region) = Dist{self.region==r};
type Redund(n:Int, r:Region){r.rank==n} = Dist{rank==n && region==r};
 }}