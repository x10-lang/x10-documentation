/*
 *  This file is part of the X10 project (http://x10-lang.org).
 *
 *  This file is licensed to You under the Eclipse Public License (EPL);
 *  You may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *      http://www.opensource.org/licenses/eclipse-1.0.php
 *
 *  (C) Copyright IBM Corporation 2006-2010.
 */

/**
 * Instances are arbitrary collections of points in a rectangular region
 * (the bounding box) with a distinction between points on the boundary
 * and in the interior of the region.  This is not meant as an efficient
 * access for generic, relatively dense regions.  It is meant as an 
 * example of how one can work X10's Region-based Arrays.  See the
 * file HeatXfer.x10 for an example of the intended use of this class.
 */

public class BlobWithBdry extends Region {
   private val box:      Region(this.rank); // bounding box supplied to constructor
   private val where:    (p: Point(this.box.rank))=>Int; // see constructor comment
   private var size:     Int = -1;   // number of points in the region: computed lazily
   private var bdrySize: Int = -1;   // number of boundary points: again, computed lazily
    
   /**
    * constructs an instance from a Region of the appropriate rank and a
    * map from Points of bounding box of that Region to Bytes with the
    * convention that
    * 
    *    where the map is negative, the Point is NOT in this Region
    *    where the map is 0 the Point is on the boundary of the Region
    *    where the map is positive, the Point is in the interior of the Region.
    * 
    * The file HeatXfer.x10 gives an example that illustrates what we mean.
    * 
    * @param box a Region, normally rectangular, that contains the Region
    *    we are constructing.
    * @param where maps Points in the bounding box of "box" to integers
    *    with the conventions described in the method comment.
    */
   public def this(box: Region, 
   		          where:(p: Point(this.box.rank)) => Int) {
      super(box.rank, false, false);
      this.box = box;
      this.where = where;
   }
   
   /**
    * Returns the number of Points in this Region.
    * @return an Int that is the the number of Points both in the boundary
    *    and the interior of the Region.
    */
   public def size(): Int {
      if (size < 0) { // not yet computed
         size = 0;
         bdrySize = 0;
         for(p in box) {
            if (where(p) > 0) size += 1;
            else if (where(p) == 0) bdrySize += 1;
         }
         size += bdrySize;
      }
      return size;
   }
   
   /**
    * Returns the number of Points in the boundary of the Region
    * @return an Int that is the number of Points p with where(p) == 0
    */
   public def boundarySize() { 
      if (size < 0) size();
      return bdrySize;
   }
   
   /**
    * Returns the number of Points in the interior of the Region
    * @return an Int that is the number of Points  Points p with where(p) 
    * positive
    */
   public def interiorSize() { 
      if (size < 0) size();
      return size - bdrySize;
   }

   /**
    * Returns true iff this region is convex.  Too expensive to compute
    * in this generality: minimally quadratic in the size of the boundary
    * and then, possibly, times the volume of the bounding box.
    * @throws UnsupportedOperationException not implemented.
    */
   public def isConvex(): Boolean {
      throw new UnsupportedOperationException("Unimplemented: too expensive");
   }

   /** 
    * Returns true when this region is empty, or in other terms, has size==0.
    * @return a Boolean: true means that there is at least one element in the Region.
    */
   public def isEmpty(): Boolean {
      if (size < 0) size();
      return size == 0;
   }
  
   /**
    * Returns the index of the argument point in the lexograpically ordered
    * enumeration of all points in the region.
    * @param p the point whose index is sought
    * @return an integer between 0 and size-1 if the point is in the region,
    * -1 otherwise.
    */
   public def indexOf(pVague: Point):Int {
   	val p = pVague as Point(box.rank);
      if (where(p) < 0) return -1;
      var index: Int = 0;
      for(q in box) {
         if ( p == q ) return index;
         else if (where(q) >= 0) index += 1;
      }
      return -1; // should never get here, but compiler will be upset if this is not here
   }
   
   /** 
    * Returns the bounding box as provided to the constructor.
    * @return a Region(rank) that is the bounding box of the actual BlobWithBdry.
    */
   public def boundingBox(): Region(rank) = box.boundingBox() as Region(rank);
   
   /** @return the bounding box */
   protected def computeBoundingBox(): Region(rank) = 
      box.computeBoundingBox();
   
   /**
    * Returns the minimum value for the i-th coordinate
    * @param i an integer in the range 0 <= i < rank
    * @return the minimum value of the i-th coordinate
    */
   public def min(i: Int):Int = box.min(i);
   /**
    * returns the minimum value for the i-th coordinate
    * @param i an integer in the range 0 <= i < rank
    * @return the minimum value of the i-th coordinate
    */
   public def max(i: Int):Int = box.max(i);
    
   /**
    * Returns a function that can be used to access the lower bounds 
    * of the bounding box of the region.
    * @return a function that computes the lower bounds for each
    * coordinate of the bounding box
    */
   public def min():(Int)=>Int = (i:Int)=> min(i);
   /**
    * Returns a function that can be used to access the lower bounds 
    * of the bounding box of the region. 
    * @return a function that computes the upper bounds for each
    * coordinate of the bounding box
    */
   public def max():(Int)=>Int = (i:Int)=> max(i);
   
   /**
    * Returns the intersection of two regions: a region that contains all
    * points that are in both this region and that region.  If only "this"
    * region is a BlobWithBdry, the mask "where" is inherited from "this", so the
    * notion of boundary and interior are unchanged.  If both are
    * BlobWithBdrys, the mask "where" is the min of the two masks, so the interior
    * of the new BlobWithBdry is the intersection of the interiors.
    * @param that the Region that is other factor in the intersection
    * @returns the BlobWithBdry that is the intersection of the two regions.
    */
   /*
    * PROGRAMMING NOTE:
    * The only safe way that you can call where(p) is to make sure that the
    * point p is in the blob's bounding box. That is why in this method and
    * the next (cartesian product) we do the check on contains(p) before
    * we try to evaluate where().
    */
   public def intersection(that: Region(rank)): Region(rank) {
       val newBox: Region(rank) = box.intersection(that.boundingBox());
       val newWhere: (p:Point(newBox.rank)) => Int;
       if(that instanceof BlobWithBdry) {
          val thatBlob = that as BlobWithBdry;
          newWhere = (p:Point(newBox.rank)) => {
         	 val thisValue = box.contains(p) ? (where(p) as Int) : -1;
         	 val thatValue = thatBlob.box.contains(p)? (thatBlob.where(p) as Int) : -1;
         	 return Math.min(thisValue, thatValue);
             };
       } else {
          newWhere = (p:Point(newBox.rank)) =>
                  that.contains(p)? where(p) : -1;
       }
       return new BlobWithBdry(newBox, newWhere);
    }
   
   /**
    * Returns the Cartesian product of "this", as the left-hand factor, with another
    * Region.
    * @param that the right-hand factor in the product
    * @return a Region{self.rank == this.rank + that.rank}
    */
   public def product(that: Region): Region{self != null} {
   	val newRank = rank + that.rank;
      if (that.isEmpty()) {
         return Region.makeEmpty(newRank);
      } 
      else {
      	val bigBox: Region(newRank) = box * that.boundingBox();
      	val newWhere: (Point)=>Int;
      	if (that instanceof BlobWithBdry) {
	      	newWhere =  (p:Point) => {
	      		val thisP = Point.make(rank, (n: Int) => p(n));
	      		val thisWhere =  box.contains(thisP) ? (where(thisP) as Int) : -1;
	         	val thatBlob = that as BlobWithBdry;
	            val thatP = Point.make(that.rank, (n: Int) => p(this.rank+n));
	            val thatWhere = thatBlob.box.contains(thatP) ? (thatBlob.where(thatP) as Int) : -1;
	            return Math.min(thisWhere, thatWhere);
	      	};
	      } 
	      else newWhere = (p: Point) => 
	                  where(Point.make(rank, (n: Int) => p(n)));
	      return new BlobWithBdry(bigBox, newWhere);
      }
   }
    
   /**
    * Returns the region shifted by a Point (vector). The Point has
    * to have the same rank as the region. A point p+v is in 
    * <code>translate(v)</code> iff <code>p</code> is in <code>this</code>. 
    */
   public def translate(v: Point(rank)): Region(rank) {
       val newBox: Region(box.rank) = box.translate(v);
       val newWhere = (p: Point(newBox.rank)) =>
                       where(p - v);
       return new BlobWithBdry(newBox, newWhere);
    }
   
    /**
     * Returns the projection of a region onto the specified axis. The
     * projection is a rank-1 region such that for every point <code>[i]</code> in
     * the projection, there is some point <code>p</code> in this region such that
     * <code>p(axis)==i</code>.
     */
   public def projection(axis: Int): Region(1) = box.projection(axis);
   
    /**
     * Returns the projection of a region onto all axes but the specified axis.
     */
   public def eliminate(axis: Int): Region = box.eliminate(axis);

   /** Return an iterator for this region */
   public def iterator():Iterator[Point(rank)]  = ARIterator.make(this);
      
   public def contains(that: Region(rank)): Boolean {
      if(!box.contains(that)) return false;
      for(p in that) if (where(p) < 0) return false;
      return true;
   }
   
   /**
    * Returns true when the Point is in the Region
    * @param p a Point of the same rank as this Region.
    * @return true when the argument in the blog: that is, when
    *    where(p) is non-negative.
    */
   public def contains(p:Point):Boolean { 
      return box.contains(p)  && where(p as Point(rank)) >= 0;
   }
   
   /**
    * Returns true when the Point is in the Region and in the Region's
    * interior.  See the constructor's comments for what "interior" means.
    * @param p a Point of the same rank as this Region.
    * @return true when the argument is in the interior of the blob:
    *    that is, when where(p) is positive.
    */
   public def isInTheInterior(p: Point(rank)) {
      return where(p) > 0;
   }
   
   /**
    * Returns true when the Point is in the Region and on the boundary
    * @param p a Point of the same rank as this Region.
    * @return true the argument  is on the boundary of the blob:
    *    that is, when where(p) is 0.
    */
   public def isOnTheBoundary(p: Point(rank)) {
      return where(p) == 0;
   }
   
   /**
    * The "AR" stands for "any region".  This is a generic class that 
    * implements Iterator for a generic BlobWithBdry.  The points are
    * traversed in lexicographic order, as usual.
    */
   private static class ARIterator(rank:Int) implements Iterator[Point(rank)] {
      val ar:   BlobWithBdry{self.rank == this.rank}; // "any region"
      var done: Boolean;                // if true, there is no next entry
      var irr:  Iterator[Point(rank)]; // an iterator for the box of ar
      var lookahead: Point(rank);      // what next() will return
      
      /**
       * We provide a factory method here because we need to read ahead to 
       * get the first element before we return the new iterator.
       * @param anyrgn the region over whose points we are iterating
       * @return the iterator ready to traverse anyrgn
       */ 
      static def make(anyrgn:BlobWithBdry): Iterator[Point(anyrgn.rank)] {
      	return new ARIterator(anyrgn).init() as Iterator[Point(anyrgn.rank)];
      }
      
      /**
       * constructs the iterator, but does not prime it: you must call init()
       * before using the iterator.
       * @param anyrgn the region over whose points we are iterating
       */
      public def this(anyrgn:BlobWithBdry) {
         property(anyrgn.rank);
         done = (anyrgn.size() == 0);
         irr = null;
         ar = anyrgn;
      }        

      /** 
       * returns true if, and only if, there remain elements to see 
       * @return true if hasNext() will produce another element
       */
      public def hasNext() = !done;

      /**
       * if there is a point remaining in the region, return it; otherwise, die.
       * @return the next point in lexicographic order.
       */
      public def next(): Point(rank) {
      	if (done) { 
      		throw new IllegalOperationException("Iterator called beyond its end.");
      	}
         val answer = lookahead;
         var gotOne: Boolean = false;
         while(irr.hasNext()) {
            lookahead = irr.next();
            if (ar.contains(lookahead)) {
               gotOne = true;
               break;
            }
         }
         done = !gotOne;
         return answer;
      }
      
      public def init() {
      	irr = ar.box.iterator() as Iterator[Point(this.rank)];
      	if (!done) next(); 
      	return this;
      }
   }
}
