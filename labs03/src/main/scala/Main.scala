object Main {
  def main(args: Array[String]): Unit = {

    if (FoldLeftRight.theorem.isGloballyValid) {
      println("The fold left-right correspondance theorem has been proved!")
    }

    if (FoldContent.theorem.isGloballyValid) {
      println("The fold with equal content correspondance theorem has been proved!")
    }
  }
}
