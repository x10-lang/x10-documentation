class MSort {
    static def msort(a:Rail[Int]):Rail[Int]
    @det@Read(a)
    {
        if (a.size <=1)
            return;
        return msort(a, new Rail[Int](a.size));
    }

    static def msort(a:Rail[Int], b:@Sole Rail[Int](a.size)):@Sole Rail[Int]{self==b}
    @det@Read(a)@Write(b)
    {
        val size = a.size;
        if (size <= 1)
            return;
        val mid = size/2;
        finish {
            async msort(a(0..mid-1), b(0..mid-1));
            msort(a(mid..size-1), b(mid..size-1));
        }
        merge(low, high, b);
        return b;
    }
    static def merge(a:Rail[Int], b:Rail[Int], c:@Sole Rail[Int]{self.size==a.size+b.size})
        : @Sole Rail[Int]{self==c}
    @Read(a)@Read(b)@Write(c)
    {
        if (a.size==1) {
            //  merge a(0) into b, and copy into c.           
        }
        val mid = a.size/2;
        val q = a((mid-1)/2);
        val r = find(q, high);
        finish {
            async merge(a(0..(mid-1)/2), b(0..r-1), c(0..((mid-1)/2)+r));
            merge(a((mid-1)/2+1..mid-1), b(r..size-mid-1), c(((mid-1)/2)+r+1, size-1));
        }
        return c;
    }
}