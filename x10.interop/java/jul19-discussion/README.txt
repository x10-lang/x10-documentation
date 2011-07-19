These are Igor's examples, modified to match the variant, described by Vijay in the letter below.

* java.lang.String is exposed as x10.lang.String
* java.lang.Object (type) is exposed as x10.lang.Any
* java.lang.Object (class) is unavailable
  - in particular, the test ``obj instanceof java.lang.Object'' is not available to X10 programmer
* boolean, byte, short, int, long are exposed as x10.lang.Boolean, Byte, Short, Int, Long
* char requires conversion (expressed as ``def convert(Char):Java.char'' in 

Please feel free to delete these examples as the design discussion moves forward.

===============================
Vijay Saraswat 	to:	Mikio Takeuchi, Kiyokuni Kawachiya, Salikh Zakirov, David P Grove, Igor Peshansky	07/15/2011 08:41 PM
--------------
Can we make the following work:

"Smooth proposal"

Below by "Java type J is exposed as X10 type X" I mean that in the X10 type
system there can be no references to J (J does not exist), the compiler
translates them into references to X.

This means that calls to Java code that use type J are thought of as calls to
the corresponding X10 code that use type X. 

The class file implementing J is not transformed in any way. When the X10
compiler emits Java code from X10, it translates X back to J.

In the X10 type system:

      jlO is exposed as xlA. Therefore methods of jlO that are not also methods
      of xlA are not available. typeName() is an additional method that is
      available and implemented by a static call.

      jlS is exposed as xlS. Note there is a concern with split -- its
      signature in xlS is different from jlS. However, this shd not be a
      problem. X10 code has to call the xlS split, the Java split is not
      available.  The X10 compiler will translate X10 calls to xlS split to
      some static call on some helper class. 

      Java int is exposed as x10.lang.Int, as are other primitive types except char.

     Java boxed primitive types  java.lang.Integer and friends continue to be
     available as types with the same name in X10.

     Existing X10 rules for conversions from X10 structs to Any apply, not Java autoboxing. i.e. 

     val x:Any = 3; 
     val y = x instanceof java.lang.Integer; // run time error

    User will have to write:

     val x:Any = 3; 
     val x0 = x as java.lang.Integer;
     val y = x0 instanceof java.lang.Integer;  


In the Java type system:

     xlA is exposed as jlO.
     xlS is exposed as jlS.

     x10.lang.Int is exposed as Java int, as are other primitive types except x10.lang.Char


Best,
Vijay
