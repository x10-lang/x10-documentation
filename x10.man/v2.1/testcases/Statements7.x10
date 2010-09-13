 package Statement.Case;
 class Example {
 def example(i : Int, println: (String)=>Void) {
switch (i) {
  case 1: println("one, and ");
  case 2: println("two");
          break;
  case 3: println("three");
          break;
  default: println("Something else");
           break;
}
 } }