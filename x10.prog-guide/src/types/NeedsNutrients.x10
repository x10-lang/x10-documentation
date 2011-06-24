import x10.util.*;

public class NeedsNutrients {

static 
//START TeX: needsnutrCaloried
interface Caloried {
  def calories():Int;
}
//END TeX: needsnutrCaloried

static 
//START TeX: needsnutrFlour
class Flour implements Caloried {
  private val name: String, cal:Int ;
  public def this(name:String, cal:Int) 
    { this.name = name; this.cal = cal; }
  public def calories() = this.cal;
}
//END TeX: needsnutrFlour

static 
//START TeX: needsnutrRecipe
class Recipe[T]{T <: Caloried} {
   val ingredients: List[T] = new ArrayList[T]();
   public def add(t:T) { ingredients.add(t); }
   public def totalCals() {
      var s : Int = 0;
      for(ingredient in ingredients) 
          s += ingredient.calories(); // \xlref{needsnutrRecipe-usecalories}
      return s;
   }
}
//END TeX: needsnutrRecipe

//START TeX: needsnutrExample
static def example(): void = {
  val flours <: Recipe[Flour] = new Recipe[Flour]();
  flours.add(new Flour("1 cup bread flour", 495));
  flours.add(new Flour("1 cup whole-wheat", 520));
  flours.add(new Flour("1 cup rye", 360));
  assert flours.totalCals() == 1375;
}
//END TeX: needsnutrExample

public static def main(Array[String](1)) {
  example();
}

}
