 package Types.Functions;
 class IncrElEx {
 static def example() throws DoomExn {
val inc = (r:Rail[Int]!, i: Int{i != r.length}) => {
  if (i < 0 || i >= r.length) throw new DoomExn();
  r(i)++;
};
}}
class DoomExn extends Exception{}