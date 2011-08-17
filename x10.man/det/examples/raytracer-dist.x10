// Partition + accumulators.
finish ateach ([pl]: Point in U) {
    val my_dist: Dist = DBlock | here;
    var checksum1: long = 0;
    var frustrumwidth: double = view.dist * Math.tan(view.angle);
    var viewVec: Vec = Vec.sub(view.att, view.from).normalized();
    var tmpVec: Vec = new Vec(viewVec).scale(Vec.dot(view.up, viewVec));
    var upVec: Vec = Vec.sub(view.up, tmpVec).normalized().scale(-frustrumwidth);
    var leftVec: Vec = Vec.cross(view.up, viewVec).normalized().scale(view.aspect * frustrumwidth);
    var r: Ray = new Ray(view.from, voidVec);

    for ([pixCounter]: Point in my_dist.region) {
        var y: int = pixCounter / interval.width;
        var x: int = pixCounter % interval.width;
        var ylen: double = (2.0 * y) / interval.width - 1.0;
        var xlen: double = (2.0 * x) / interval.width - 1.0;
        r = r.d (Vec.comb(xlen, leftVec, ylen, upVec).added(viewVec).normalized());
        var col: Vec = trace(0, 1.0, r, new Isect(), new Ray());

        // computes the color of the ray
        var red: int = (col.x * 255.0) as int;
        if (red > 255) red = 255;
        var green: int = (col.y * 255.0) as int;
        if (green > 255) green = 255;
        var blue: int = (col.z * 255.0) as int;
        if (blue > 255) blue = 255;

        checksum1 += red + green + blue;
        // RGB values for .ppm file
        // Sets the pixels
        //row[pixCounter/*++*/] =  alpha | (red << 16) | (green << 8) | (blue);
    }
    val checksumx: long = checksum1;
    finish async at (Place.FIRST_PLACE) {
        atomic { checksum += checksumx; }
    }
}
