package Arrays.Arrays.Arrays.Example;
 class Example{
static def addInto(src: Array[Int], dest:Array[Int])
  {src.region == dest.region}
  = {
    for (p in src.region)
       dest(p) += src(p);
  }
}