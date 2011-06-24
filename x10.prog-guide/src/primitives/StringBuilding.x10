public class StringBuilding {
  public static def main(argv:Array[String](1)) {
//START TeX: stringbuilding
    val sb = new StringBuilder();
    sb.add(2);
    sb.add(" and ");
    sb.add(3.0);
    sb.add(" is "+5.0);
    val s = sb.result();
    assert s.equals("2 and 3.0 is 5.0");
//END TeX: stringbuilding
  }
}
