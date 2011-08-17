class Tree (@ersatz up:Tree, @ersatz left:Boolean) {
    var left:Tree{self.up==this, self.left==true};
    var right:Tree{self.up==this, self.left==false};
    var mass:Double;
    var force:Double;
    var link:Tree;
    static def make(up:Tree, left:Boolean):Tree{self.up==up,self.left==left} {
        val x = new Tree(up, left);
        x.left = new Tree(x, true);
        x.right = new Tree(x, false);
        return x;
    }
    def computeForce()
        @Write(Tree{i:UInt^self.up$i=this}.force)
        @Read(Tree{i:UInt^self.up$i=this}.left)              ]
        @Read(Tree{i:UInt^self.up$i=this}.right)
        @Read(Tree.mass)            
    {
        finish {
            @Write(Tree{self==this}.mass)
                async this.force = (this.mass*link.mass)*G;

            if (left != null)
                async left.computeForce();
            if (right != null)
                async right.computeForce();
        }
    }
}