class Tree (@ersatz up:Tree, @ersatz left:Boolean) {
    var left:Tree{self.up==this, self.left==true};
    var right:Tree{self.up==this, self.left==false};
    var cargo:Int;
    static def make(up:Tree, left:Boolean):Tree{self.up==up,self.left==left} {
        val x = new Tree(up, left);
        x.left = new Tree(x, true);
        x.right = new Tree(x, false);
        return x;
    }
    def makeConstant(x:Int)
        @Write(Tree{i:UInt^self.up$i=this}.cargo)
        @Read(Tree{i:UInt^self.up$i=this}.left)              ]
            @Read(Tree{i:UInt^self.up$i=this}.right)
    {
        finish {
            @Write(Tree{self==this}.cargo)
            this.cargo = x;
            if (left != null)
                async
                    @Write(Tree{i:UInt^(self.up$i.up=this,self.up$i.left==true)}.cargo)
                    left.makeConstant(x);
            if (right != null)
                @Write(Tree{i:UInt^(self.up$i.up==this,self.up$i.left==false)}.cargo)
                async right.makeConstant(x);
        }
    }
}