class Tree (@ersatz up:Tree, @ersatz left:Boolean) {
    var left:Tree{self.up==this, self.left==true};
    var right:Tree{self.up==this, self.left==false};
    var mass:Double;
    var force:Double;
    static def make(up:Tree, left:Boolean):Tree{self.up==up,self.left==left} {
        val x = new Tree(up, left);
        x.left = new Tree(x, true);
        x.right = new Tree(x, false);
        return x;
    }
    def makeConstant(mass:Double, force:Double)
        @Write(Tree{i:UInt^self.up$i=this}.(mass,force))
        @Read(Tree{i:UInt^self.up$i=this}.left)              ]
            @Read(Tree{i:UInt^self.up$i=this}.right)
    {
        finish {
            @Write(Tree{self==this}.mass)
            async this.mass = mass;

            @Write(Tree{self==this}.force)
            async this.force = force;            

            if (left != null)
                async left.makeConstant(mass,force);
            if (right != null)
                async right.makeConstant(mass, force);
        }
    }
}