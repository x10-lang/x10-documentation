class BarnesHut {

    static abstract class  Node {
        var mass:Double;
        var pos:Vector[Int];
    }

    static class InnerNode extends Node {
        val children:Array[@Sole Node];
    }
    static class LeafNode extends Node {
        val body:Body;
    }
    static class Body  {
        val force:Vector[Double];

        def computeForce(subtree:Node):Vector[Double]
            @Read (root.(children(_))*.(mass + pos))
        {
            //
        }
    }

    static class Tree {
        val root:Node;
        val bodies:@Distinct Array[Body];

        def computeForces():void {
          finish  for (body in bodies.values())
              async
                  @Read(root.(children(_))*.(mass+pos))
                  @Write(body.force)
                  {
                      body.force = body.computeForce(root);
                  }
                
        }
    }
}