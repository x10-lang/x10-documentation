interface ExtendingInterfaces {
//START TeX: extendinginterfaces
interface Colored {
  def color(): Int;
}
interface Shape{}
interface Shaped {
  def shape():Shape;
}
interface ColorForm extends Colored, Shaped {}
//END TeX: extendinginterfaces
}
